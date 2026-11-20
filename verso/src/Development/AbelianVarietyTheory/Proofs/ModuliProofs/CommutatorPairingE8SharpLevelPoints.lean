import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpWeil

section Abstract
variable {G C : Type} [CommGroup G] [CommGroup C] {k : ℕ}

/- English proof (translation)
Take `⟨c, hc, hu⟩` from `hex 1 (one_pow k)`. Establish `hcc : c * c = c` using `hu _ (by simpa using hmul 1 1 c c hc hc)`. Establish `hc1 : c = 1` using `by simpa using hcc`. Rewrite `hc` using `[hc1]`. Then use the resulting hypothesis.
-/
private theorem rel_one_one {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) : R 1 1 := by
  obtain ⟨c, hc, hu⟩ := hex 1 (one_pow k)
  have hcc : c * c = c := hu _ (by simpa using hmul 1 1 c c hc hc)
  have hc1 : c = 1 := by simpa using hcc
  rwa [hc1] at hc

/- English proof (translation)
Take `⟨d, hd, -⟩` from `hex x⁻¹ (by rw [inv_pow, hx, inv_one])`. Establish `h1 : R 1 (c * d)` using `by simpa using hmul _ _ _ _ h hd`. Take `⟨e, -, hu⟩` from `hex 1 (one_pow k)`. Establish `hcd : c * d = 1` using `(hu _ h1).trans (hu _ (rel_one_one hex hmul)).symm`. Rewrite `hd` using `[eq_inv_of_mul_eq_one_right hcd]`. Then use the resulting hypothesis.
-/
private theorem rel_inv_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (hx : x ^ k = 1)
    (h : R x c) : R x⁻¹ c⁻¹ := by
  obtain ⟨d, hd, -⟩ := hex x⁻¹ (by rw [inv_pow, hx, inv_one])
  have h1 : R 1 (c * d) := by simpa using hmul _ _ _ _ h hd
  obtain ⟨e, -, hu⟩ := hex 1 (one_pow k)
  have hcd : c * d = 1 := (hu _ h1).trans (hu _ (rel_one_one hex hmul)).symm
  rwa [eq_inv_of_mul_eq_one_right hcd] at hd

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using rel_one_one hex hmul`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `hmul _ _ _ _ ih h`.
-/
private theorem rel_pow_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (h : R x c) (n : ℕ) :
    R (x ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using rel_one_one hex hmul
  | succ n ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => simpa using rel_pow_of_rel hex hmul h n`. Consider the case `negSucc n`. Rewrite using `[zpow_negSucc, zpow_negSucc]`. Conclude with `rel_inv_of_rel hex hmul (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) (rel_pow_of_rel hex hmul h (n + 1))`.
-/
private theorem rel_zpow_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (hx : x ^ k = 1)
    (h : R x c) (n : ℤ) : R (x ^ n) (c ^ n) := by
  cases n with
  | ofNat n => simpa using rel_pow_of_rel hex hmul h n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc]
    exact rel_inv_of_rel hex hmul (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) (rel_pow_of_rel hex hmul h (n + 1))

/- English proof (translation)
Use `Finset.induction_on s (by simpa using rel_one_one hex hmul) ?_` and prove the remaining obligations. Introduce `i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.prod_insert hi]`. Conclude with `hmul _ _ _ _ (rel_zpow_of_rel hex hmul (hq i) (h i) (a i)) ih`.
-/
theorem rel_prod {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {I : Type} (s : Finset I) (q : I → G) (c : I → C)
    (hq : ∀ i, q i ^ k = 1) (h : ∀ i, R (q i) (c i)) (a : I → ℤ) :
    R (∏ i ∈ s, q i ^ a i) (∏ i ∈ s, c i ^ a i) := by
  classical
  refine Finset.induction_on s (by simpa using rel_one_one hex hmul) ?_
  intro i s hi ih
  rw [Finset.prod_insert hi, Finset.prod_insert hi]
  exact hmul _ _ _ _ (rel_zpow_of_rel hex hmul (hq i) (h i) (a i)) ih

/- English proof (translation)
Rewrite using `[← Finset.prod_pow]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm (a i), zpow_mul, zpow_natCast, hq i, one_zpow]`.
-/
theorem prod_zpow_pow {I : Type} [Fintype I] (q : I → G) (hq : ∀ i, q i ^ k = 1) (a : I → ℤ) :
    (∏ i, q i ^ a i) ^ k = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm (a i), zpow_mul, zpow_natCast, hq i, one_zpow]

/- English proof (translation)
Use `Finset.induction_on s (by simp) ?_` and prove the remaining obligations. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]`.
-/
theorem zpow_sum' {I : Type} (s : Finset I) (ζ : C) (a : I → ℤ) : ζ ^ (∑ i ∈ s, a i) = ∏ i ∈ s, ζ ^ a i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

/- English proof (translation)
Establish `hy : (∏ j, q j ^ b j) ^ k = 1` using `prod_zpow_pow q hq b`. Establish `hrow : ∀ i, R (q i) (∏ j, q j ^ b j) (ζ ^ ∑ j, b j * ω i j)`. Introduce `i`. Establish `H : R (∏ j, q j ^ b j) (q i) (∏ j, ((ζ ^ ω i j)⁻¹) ^ b j)` using `rel_prod (R := fun x c => R x (q i) c) (fun x hx => hex x (q i) hx (hq i)) (fun x x' c c' h1 h2 => hmul x x' (q i) c c' h1 h2) Finset.univ q (fun j => (ζ ^ ω i j)⁻¹) hq (fun j => hsymm _ _ _ (h i j)) b`. Establish `e : ζ ^ ∑ j, b j * ω i j = (∏ j, ((ζ ^ ω i j)⁻¹) ^ b j)⁻¹`.

Rewrite using `[zpow_sum', ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[inv_zpow, inv_inv, ← zpow_mul, mul_comm (b j)]`. Rewrite using `[e]`. Conclude with `hsymm _ _ _ H`.

Establish `H : R (∏ i, q i ^ a i) (∏ j, q j ^ b j) (∏ i, (ζ ^ ∑ j, b j * ω i j) ^ a i)` using `rel_prod (R := fun x c => R x (∏ j, q j ^ b j) c) (fun x hx => hex x _ hx hy) (fun x x' c c' h1 h2 => hmul x x' _ c c' h1 h2) Finset.univ q (fun i => ζ ^ ∑ j, b j * ω i j) hq hrow a`. Establish `e : ζ ^ ∑ i, ∑ j, a i * b j * ω i j = ∏ i, (ζ ^ ∑ j, b j * ω i j) ^ a i`. Rewrite using `[zpow_sum']`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_mul, Finset.sum_mul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `H`.
-/
theorem rel_biprod {R : G → G → C → Prop} (hex : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, R x y c)
    (hmul : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c'))
    (hsymm : ∀ x y c, R x y c → R y x c⁻¹) {I : Type} [Fintype I] (q : I → G) (ζ : C) (ω : I → I → ℤ)
    (hq : ∀ i, q i ^ k = 1) (h : ∀ i j, R (q i) (q j) (ζ ^ ω i j)) (a b : I → ℤ) :
    R (∏ i, q i ^ a i) (∏ i, q i ^ b i) (ζ ^ ∑ i, ∑ j, a i * b j * ω i j) := by
  have hy : (∏ j, q j ^ b j) ^ k = 1 := prod_zpow_pow q hq b
  have hrow : ∀ i, R (q i) (∏ j, q j ^ b j) (ζ ^ ∑ j, b j * ω i j) := by
    intro i
    have H : R (∏ j, q j ^ b j) (q i) (∏ j, ((ζ ^ ω i j)⁻¹) ^ b j) :=
      rel_prod (R := fun x c => R x (q i) c) (fun x hx => hex x (q i) hx (hq i))
        (fun x x' c c' h1 h2 => hmul x x' (q i) c c' h1 h2) Finset.univ q (fun j => (ζ ^ ω i j)⁻¹) hq
        (fun j => hsymm _ _ _ (h i j)) b
    have e : ζ ^ ∑ j, b j * ω i j = (∏ j, ((ζ ^ ω i j)⁻¹) ^ b j)⁻¹ := by
      rw [zpow_sum', ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [inv_zpow, inv_inv, ← zpow_mul, mul_comm (b j)]
    rw [e]
    exact hsymm _ _ _ H
  have H : R (∏ i, q i ^ a i) (∏ j, q j ^ b j) (∏ i, (ζ ^ ∑ j, b j * ω i j) ^ a i) :=
    rel_prod (R := fun x c => R x (∏ j, q j ^ b j) c) (fun x hx => hex x _ hx hy)
      (fun x x' c c' h1 h2 => hmul x x' _ c c' h1 h2) Finset.univ q (fun i => ζ ^ ∑ j, b j * ω i j) hq hrow a
  have e : ζ ^ ∑ i, ∑ j, a i * b j * ω i j = ∏ i, (ζ ^ ∑ j, b j * ω i j) ^ a i := by
    rw [zpow_sum']
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact H

end Abstract

/- English proof (translation)
Apply `bas.symm.injective` to reduce the goal to its premises. Rewrite using `[map_sum]`. Simplify using `only [map_zsmul, LinearEquiv.symm_apply_apply]`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem eq_sum_basis {n : ℕ} {M : Type} [AddCommGroup M] (bas : (Fin n → ℤ) ≃ₗ[ℤ] M) (X : M) :
    X = ∑ i, bas.symm X i • bas (Pi.single i 1) := by
  apply bas.symm.injective
  rw [map_sum]
  simp only [map_zsmul, LinearEquiv.symm_apply_apply]
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

def omegaLin (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ omegaStd
    (fun a a' b => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)
    (fun a b b' => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)

/- English proof (translation)
Establish `hω : ∀ a b : Fin h ⊕ Fin h → ℤ, omegaStd a b = omegaLin h a b` using `fun a b => by simp [omegaLin]`. Establish `hX : ∀ u, X u = ∑ i, bas.symm X i • bas (Pi.single i 1) u` using `fun u => by conv_lhs => rw [eq_sum_basis bas X]`. Simplify using `[Finset.sum_apply]`. Establish `hY : ∀ v, Y v = ∑ j, bas.symm Y j • bas (Pi.single j 1) v` using `fun v => by conv_lhs => rw [eq_sum_basis bas Y]`. Simplify using `[Finset.sum_apply]`.

Establish `hs : ∀ i j, Out.stdSymp g i j = ∑ u, ∑ v, (W + W.transpose) u v * omegaLin h (bas (Pi.single i 1) u) (bas (Pi.single j 1) v)` using `fun i j => by`. Rewrite using `[← hb i j]`. Simplify using `only [hω]`. Simplify using `only [hs, hω, hX, hY, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `(Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans ?_` and prove the remaining obligations.

Use `Finset.sum_comm.trans ?_` and prove the remaining obligations. Use `(Finset.sum_congr rfl fun i _ => (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_` and prove the remaining obligations. Use `Finset.sum_comm.trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_eq {h g : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hb : IsSharpBasis W bas)
    (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) :
    ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v) =
      ∑ i, ∑ j, bas.symm X i * bas.symm Y j * Out.stdSymp g i j := by
  have hω : ∀ a b : Fin h ⊕ Fin h → ℤ, omegaStd a b = omegaLin h a b := fun a b => by simp [omegaLin]
  have hX : ∀ u, X u = ∑ i, bas.symm X i • bas (Pi.single i 1) u := fun u => by
    conv_lhs => rw [eq_sum_basis bas X]
    simp [Finset.sum_apply]
  have hY : ∀ v, Y v = ∑ j, bas.symm Y j • bas (Pi.single j 1) v := fun v => by
    conv_lhs => rw [eq_sum_basis bas Y]
    simp [Finset.sum_apply]
  have hs : ∀ i j, Out.stdSymp g i j = ∑ u, ∑ v, (W + W.transpose) u v *
      omegaLin h (bas (Pi.single i 1) u) (bas (Pi.single j 1) v) := fun i j => by
    rw [← hb i j]; simp only [hω]
  simp only [hs, hω, hX, hY, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun i _ =>
    (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `hc` using `congrArg (fun f : Sp K ⟶ Sp o => f.appTop.hom (unitOn u).val) hp`. Simplify using `only [unitS, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hc ⊢`. Rewrite using `[hc]`. Unfold `unitOn spMap Sp`.

Establish `hn` using `congrArg (fun φ => φ.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn`. Simplify using `only [Units.coe_map, hz]`. Conclude with `hn.symm`.
-/
theorem pull_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (p : Sp K ⟶ S)
    (β : o →+* K) (u : oˣ) (z : Kˣ) (hp : p ≫ s = spMap β) (hz : (z : K) = β u) :
    Units.map p.appTop.hom.toMonoidHom (unitS s u) = unitOn z := by
  apply Units.ext
  have hc := congrArg (fun f : Sp K ⟶ Sp o => f.appTop.hom (unitOn u).val) hp
  simp only [unitS, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply] at hc ⊢
  rw [hc]
  unfold unitOn spMap Sp
  have hn := congrArg (fun φ => φ.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  simp only [Units.coe_map, hz]
  exact hn.symm

end GlobalTheory.SharpWeil

namespace GlobalTheory

open SharpWeil in

/- English proof (translation)
Introduce `hL h g W J bas k o _ b S _ s t A _ _ pr lev hb hpr huniv hlev hpt K _ p β z hps hz X Y y y' hy hy'`. Use `t.ab.comm` as an intermediate fact. Set `e : Over.mk p ⟶ Out.baseOver S` to `Over.homMk p (by simp)`. Set `q : Fin (2 * g) → (Over.mk p ⟶ t.A)` to `fun i => e ≫ t.pt i`. Take `⟨hex, hmul, -, -⟩` from `hL.weil S t.pol k (Over.mk p)`.

Establish `hq : ∀ i, q i ^ k = 1` using `fun i => by`. Simplify using `only [q]`. Rewrite using `[← MonObj.comp_pow, t.torsion i, MonObj.comp_one]`. Establish `hpair : ∀ i j, Out.WeilIs t.A t.L k (q i) (q j) (unitOn z ^ Out.stdSymp g i j)` using `fun i j => by`. Establish `H` using `CommPairing.weilIs_pull hL.globalFns t.ab t.isLB e (t.pairing i j)`.

Establish `e1 : Units.map e.left.appTop.hom.toMonoidHom (unitS s b.ζ) = unitOn z` using `pull_unitS s p β b.ζ z hps hz`. Rewrite `H` using `[map_zpow, e1]`. Then use the resulting hypothesis. Establish `htu : (toUnit (Over.mk p)).left = e.left` using `congrArg Over.Hom.left (toUnit_unique (toUnit (Over.mk p)) (Over.homMk p (by simp) : Over.mk p ⟶ 𝟙_ (Over S)))`. Establish `hqlev : ∀ i u, q i ≫ pr u = toUnit (Over.mk p) ≫ lev (bas (Pi.single i 1) u)` using `fun i u => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Simplify using `only [q]`. Rewrite using `[Category.assoc, Over.comp_left, hpt i u, Over.comp_left, htu]`. Set `levHom : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (𝟙_ (Over S) ⟶ A)` to `MonoidHom.mk' (fun a => lev a.toAdd) (fun a c => hlev _ _)`. Set `ψ : (𝟙_ (Over S) ⟶ A) →* (Over.mk p ⟶ A)` to `MonoidHom.mk' (fun f => toUnit (Over.mk p) ≫ f) (fun f f' => MonObj.comp_mul _ f f')`. Establish `hprod : ∀ (V : Fin 8 → Fin h ⊕ Fin h → ℤ) (w : Over.mk p ⟶ t.A), (∀ u, w ≫ pr u = toUnit (Over.mk p) ≫ lev (V u)) → w = ∏ i, q i ^ bas.symm V i`.

Introduce `V w hw`. Take `⟨x0, -, hu⟩` from `huniv (Over.mk p) (fun u => w ≫ pr u)`. Use `(hu w fun u => rfl).trans (hu _ fun u => ?_).symm` and prove the remaining obligations. Use `hpr u` as an intermediate fact. Set `φ : (Over.mk p ⟶ t.A) →* (Over.mk p ⟶ A)` to `MonoidHom.mk' (fun x => x ≫ pr u) (fun a c => MonObj.mul_comp a c (pr u))`.

Establish `hV : V u = ∑ i, bas.symm V i • bas (Pi.single i 1) u` using `by conv_lhs => rw [eq_sum_basis bas V]`. Simplify using `[Finset.sum_apply]`. Establish `h1 : (∏ i, q i ^ bas.symm V i) ≫ pr u = ∏ i, (q i ≫ pr u) ^ bas.symm V i`. Express the relevant statement in the definitionally equal form `φ (∏ i, q i ^ bas.symm V i) = ∏ i, (φ (q i)) ^ bas.symm V i`. Simplify using `only [map_prod, map_zpow]`.

Establish `h2 : toUnit (Over.mk p) ≫ lev (V u) = ∏ i, (toUnit (Over.mk p) ≫ lev (bas (Pi.single i 1) u)) ^ bas.symm V i`. Express the relevant statement in the definitionally equal form `ψ (levHom (Multiplicative.ofAdd (V u))) = ∏ i, (ψ (levHom (Multiplicative.ofAdd (bas (Pi.single i 1) u)))) ^ bas.symm V i`. Rewrite using `[hV, ofAdd_sum]`. Simplify using `only [ofAdd_zsmul, map_prod, map_zpow]`. Rewrite using `[h1, hw u, h2]`.

Conclude with `Finset.prod_congr rfl fun i _ => by rw [hqlev i u]`. Rewrite using `[form_eq hb X Y, hprod X y hy, hprod Y y' hy']`. Conclude with `rel_biprod (R := fun a c d => Out.WeilIs t.A t.L k a c d) (fun a c ha hc => hex a c ha hc) (fun a a' c d d' h1 h2 => hmul a a' c d d' h1 h2) (fun a c d H => CommPairing.weilIs_symm t.isLB H) q (unitOn z) (Out.stdSymp g) hq hpair (bas.symm X) (bas.symm Y)`.
-/
theorem weilIs_sharp_levelPoints : Out.Laws → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), IsSharpBasis W bas → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → ∀ (K : Type) [Field K] (p : Sp K ⟶ S) (β : o →+* K) (z : Kˣ), p ≫ s = spMap β → (z : K) = β b.ζ → ∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ t.A), (∀ u, y ≫ pr u = toUnit _ ≫ lev (X u)) → (∀ u, y' ≫ pr u = toUnit _ ≫ lev (Y u)) → Out.WeilIs t.A t.L k y y' (unitOn z ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v)) := by
  intro hL h g W J bas k o _ b S _ s t A _ _ pr lev hb hpr huniv hlev hpt K _ p β z hps hz X Y y y' hy hy'
  have := t.ab.comm
  let e : Over.mk p ⟶ Out.baseOver S := Over.homMk p (by simp)
  let q : Fin (2 * g) → (Over.mk p ⟶ t.A) := fun i => e ≫ t.pt i
  obtain ⟨hex, hmul, -, -⟩ := hL.weil S t.pol k (Over.mk p)
  have hq : ∀ i, q i ^ k = 1 := fun i => by
    simp only [q]
    rw [← MonObj.comp_pow, t.torsion i, MonObj.comp_one]
  have hpair : ∀ i j, Out.WeilIs t.A t.L k (q i) (q j) (unitOn z ^ Out.stdSymp g i j) := fun i j => by
    have H := CommPairing.weilIs_pull hL.globalFns t.ab t.isLB e (t.pairing i j)
    have e1 : Units.map e.left.appTop.hom.toMonoidHom (unitS s b.ζ) = unitOn z := pull_unitS s p β b.ζ z hps hz
    rwa [map_zpow, e1] at H
  have htu : (toUnit (Over.mk p)).left = e.left :=
    congrArg Over.Hom.left (toUnit_unique (toUnit (Over.mk p)) (Over.homMk p (by simp) : Over.mk p ⟶ 𝟙_ (Over S)))
  have hqlev : ∀ i u, q i ≫ pr u = toUnit (Over.mk p) ≫ lev (bas (Pi.single i 1) u) := fun i u => by
    apply Over.OverMorphism.ext
    simp only [q]
    rw [Category.assoc, Over.comp_left, hpt i u, Over.comp_left, htu]
  let levHom : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (𝟙_ (Over S) ⟶ A) :=
    MonoidHom.mk' (fun a => lev a.toAdd) (fun a c => hlev _ _)
  let ψ : (𝟙_ (Over S) ⟶ A) →* (Over.mk p ⟶ A) :=
    MonoidHom.mk' (fun f => toUnit (Over.mk p) ≫ f) (fun f f' => MonObj.comp_mul _ f f')
  have hprod : ∀ (V : Fin 8 → Fin h ⊕ Fin h → ℤ) (w : Over.mk p ⟶ t.A),
      (∀ u, w ≫ pr u = toUnit (Over.mk p) ≫ lev (V u)) → w = ∏ i, q i ^ bas.symm V i := by
    intro V w hw
    obtain ⟨x0, -, hu⟩ := huniv (Over.mk p) (fun u => w ≫ pr u)
    refine (hu w fun u => rfl).trans (hu _ fun u => ?_).symm
    have := hpr u
    let φ : (Over.mk p ⟶ t.A) →* (Over.mk p ⟶ A) :=
      MonoidHom.mk' (fun x => x ≫ pr u) (fun a c => MonObj.mul_comp a c (pr u))
    have hV : V u = ∑ i, bas.symm V i • bas (Pi.single i 1) u := by
      conv_lhs => rw [eq_sum_basis bas V]
      simp [Finset.sum_apply]
    have h1 : (∏ i, q i ^ bas.symm V i) ≫ pr u = ∏ i, (q i ≫ pr u) ^ bas.symm V i := by
      change φ (∏ i, q i ^ bas.symm V i) = ∏ i, (φ (q i)) ^ bas.symm V i
      simp only [map_prod, map_zpow]
    have h2 : toUnit (Over.mk p) ≫ lev (V u) =
        ∏ i, (toUnit (Over.mk p) ≫ lev (bas (Pi.single i 1) u)) ^ bas.symm V i := by
      change ψ (levHom (Multiplicative.ofAdd (V u))) =
        ∏ i, (ψ (levHom (Multiplicative.ofAdd (bas (Pi.single i 1) u)))) ^ bas.symm V i
      rw [hV, ofAdd_sum]
      simp only [ofAdd_zsmul, map_prod, map_zpow]
    rw [h1, hw u, h2]
    exact Finset.prod_congr rfl fun i _ => by rw [hqlev i u]
  rw [form_eq hb X Y, hprod X y hy, hprod Y y' hy']
  exact rel_biprod (R := fun a c d => Out.WeilIs t.A t.L k a c d) (fun a c ha hc => hex a c ha hc)
    (fun a a' c d d' h1 h2 => hmul a a' c d d' h1 h2) (fun a c d H => CommPairing.weilIs_symm t.isLB H)
    q (unitOn z) (Out.stdSymp g) hq hpair (bas.symm X) (bas.symm Y)

end GlobalTheory
end
