import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.Vonto

/- English proof (translation)
Establish `e3 : ∀ i k, ∑ j, (W i j + W j i) * C j k = if i = k then 1 else 0` using `fun i k => by`. Use `congrFun (congrFun h i) k` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `using this`. Establish `e1 : ∀ i, ∑ j, W i j • ((∑ k, C j k • a i k) + ∑ k, C i k • a j k) = ∑ j, W i j • ∑ k, C j k • a i k + ∑ j, W i j • ∑ k, C i k • a j k` using `fun i => by`.

Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => smul_add _ _ _`. Rewrite using `[Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib]`. Rewrite using `[show (∑ i, ∑ j, W i j • ∑ k, C i k • a j k) = ∑ i, ∑ j, W j i • ∑ k, C j k • a i k from Finset.sum_comm]`. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Repeatedly rewrite using `[← add_smul, Finset.smul_sum, ← mul_smul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul, e3, ite_smul, one_smul, zero_smul]`.

Simplify using the standard rewrite rules.
-/
theorem sum_sym_inv {G : Type} [AddCommGroup G] {r : ℕ} (W C : Matrix (Fin r) (Fin r) ℤ)
    (h : (W + W.transpose) * C = 1) (a : Fin r → Fin r → G) :
    ∑ i, ∑ j, W i j • ((∑ k, C j k • a i k) + ∑ k, C i k • a j k) = ∑ i, a i i := by
  have e3 : ∀ i k, ∑ j, (W i j + W j i) * C j k = if i = k then 1 else 0 := fun i k => by
    have := congrFun (congrFun h i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa using this
  have e1 : ∀ i, ∑ j, W i j • ((∑ k, C j k • a i k) + ∑ k, C i k • a j k) =
      ∑ j, W i j • ∑ k, C j k • a i k + ∑ j, W i j • ∑ k, C i k • a j k := fun i => by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => smul_add _ _ _
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib]
  rw [show (∑ i, ∑ j, W i j • ∑ k, C i k • a j k) = ∑ i, ∑ j, W j i • ∑ k, C j k • a i k from Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_smul, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, e3, ite_smul, one_smul, zero_smul]
  simp

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

section Split

variable {X U : Type} [AddCommGroup X] [CommGroup U]

@[ext] structure ExtPt (f : X → X → U) where

  a : X

  u : U

instance (f : X → X → U) : Add (ExtPt f) := ⟨fun p q => ⟨p.a + q.a, p.u * q.u / f p.a q.a⟩⟩

instance (f : X → X → U) : Zero (ExtPt f) := ⟨⟨0, 1⟩⟩

instance (f : X → X → U) : Neg (ExtPt f) := ⟨fun p => ⟨-p.a, f p.a (-p.a) / p.u⟩⟩

def extGroup (f : X → X → U) (f0 : ∀ a, f 0 a = 1) (fs : ∀ a b, f a b = f b a)
    (fc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) : AddCommGroup (ExtPt f) where
  add_assoc p q w := by
    refine ExtPt.ext (add_assoc p.a q.a w.a) ?_
    change p.u * q.u / f p.a q.a * w.u / f (p.a + q.a) w.a = p.u * (q.u * w.u / f q.a w.a) / f p.a (q.a + w.a)
    have h := congrArg Additive.ofMul (fc p.a q.a w.a)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at h ⊢
    linear_combination (norm := abel) -h
  zero_add p := by
    refine ExtPt.ext (zero_add p.a) ?_
    change 1 * p.u / f 0 p.a = p.u
    rw [f0, _root_.one_mul, div_one]
  add_zero p := by
    refine ExtPt.ext (add_zero p.a) ?_
    change p.u * 1 / f p.a 0 = p.u
    rw [fs, f0, _root_.mul_one, div_one]
  neg_add_cancel p := by
    refine ExtPt.ext (neg_add_cancel p.a) ?_
    change f p.a (-p.a) / p.u * p.u / f (-p.a) p.a = 1
    rw [fs (-p.a), div_mul_cancel, div_self']
  add_comm p q := by
    refine ExtPt.ext (add_comm p.a q.a) ?_
    change p.u * q.u / f p.a q.a = q.u * p.u / f q.a p.a
    rw [mul_comm p.u, fs]
  nsmul := nsmulRec
  zsmul := zsmulRec

/- English proof (translation)
Use `letI := extGroup f f0 fs fc`. Set `bX` to `Module.Free.chooseBasis ℤ X`. Set `h : X →ₗ[ℤ] ExtPt f` to `bX.constr ℤ fun i => ⟨bX i, 1⟩`. Set `p : ExtPt f →ₗ[ℤ] X` to `AddMonoidHom.toIntLinearMap ⟨⟨ExtPt.a, rfl⟩, fun _ _ => rfl⟩`. Establish `hp : p ∘ₗ h = LinearMap.id` using `bX.ext fun i => by`.

Express the relevant statement in the definitionally equal form `(h (bX i)).a = bX i`. Simplify using `only [h, bX.constr_basis]`. Establish `ha : ∀ x, (h x).a = x` using `fun x => LinearMap.congr_fun hp x`. Use `⟨fun x => (h x).u, fun a b => ?_⟩` and prove the remaining obligations. Establish `e : (h (a + b)).u = (h a).u * (h b).u / f (h a).a (h b).a` using `congrArg ExtPt.u (map_add h a b)`.

Use `show (h (a + b)).u * f a b = (h a).u * (h b).u`. Rewrite using `[e, ha, ha, div_mul_cancel]`.
-/
theorem exists_split [Module.Free ℤ X] (f : X → X → U) (f0 : ∀ a, f 0 a = 1) (fs : ∀ a b, f a b = f b a)
    (fc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) :
    ∃ s : X → U, ∀ a b, s (a + b) * f a b = s a * s b := by
  letI := extGroup f f0 fs fc
  let bX := Module.Free.chooseBasis ℤ X
  let h : X →ₗ[ℤ] ExtPt f := bX.constr ℤ fun i => ⟨bX i, 1⟩
  let p : ExtPt f →ₗ[ℤ] X := AddMonoidHom.toIntLinearMap ⟨⟨ExtPt.a, rfl⟩, fun _ _ => rfl⟩
  have hp : p ∘ₗ h = LinearMap.id := bX.ext fun i => by
    change (h (bX i)).a = bX i
    simp only [h, bX.constr_basis]
  have ha : ∀ x, (h x).a = x := fun x => LinearMap.congr_fun hp x
  refine ⟨fun x => (h x).u, fun a b => ?_⟩
  have e : (h (a + b)).u = (h a).u * (h b).u / f (h a).a (h b).a := congrArg ExtPt.u (map_add h a b)
  show (h (a + b)).u * f a b = (h a).u * (h b).u
  rw [e, ha, ha, div_mul_cancel]

end Split

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_split (fun χ χ' => N.θ (N.c χ) (N.c χ') b) (fun a => by rw [N.c_zero, N.cub.face]) (fun a a' => N.cub.s01 _ _ _) (fun a a' a'' => by simp only [N.c_add]; exact N.cub.coc _ _ _ _)`. Conclude with `⟨⟨b, s, hs⟩, rfl⟩`.
-/
theorem exists_gt_over {F : Type} [Field F] (N : NumD F) (b : N.A) : ∃ g : N.Gt, g.b = b := by
  obtain ⟨s, hs⟩ := exists_split (fun χ χ' => N.θ (N.c χ) (N.c χ') b)
    (fun a => by rw [N.c_zero, N.cub.face]) (fun a a' => N.cub.s01 _ _ _)
    (fun a a' a'' => by simp only [N.c_add]; exact N.cub.coc _ _ _ _)
  exact ⟨⟨b, s, hs⟩, rfl⟩

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

/- English proof (translation)
Take `⟨hφm, -, hem, heb, -, -, -, -⟩` from `hT`. Establish `hBC : (W + W.transpose) * (W + W.transpose)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hdet`. Set `E : N'.X ≃+ (Fin r → N.X)` to `AddEquiv.ofBijective (AddMonoidHom.mk' e fun a b => funext (hem a b)) heb`. Set `sH : Fin r → Multiplicative N.X →* Fˣ` to `fun k => t'.comp (AddMonoidHom.toMultiplicative ((E.symm : (Fin r → N.X) →+ N'.X).comp (AddMonoidHom.single (fun _ : Fin r => N.X) k)))`. Set `C` to `(W + W.transpose)⁻¹`.

Use `⟨fun j => ∏ k, sH k ^ C j k, fun j => ?_, fun χ' => ?_⟩` and prove the remaining obligations. Establish `h1` using `hφm 1 1 j`. Rewrite `h1` using `[_root_.mul_one]`. Conclude with `mul_eq_left.1 h1.symm`. Establish `hχ : χ' = ∑ i, E.symm (Pi.single i (e χ' i))`.

Rewrite using `[← map_sum, Finset.univ_sum_single]`. Conclude with `(E.symm_apply_apply χ').symm`. Establish `ht : t' (Multiplicative.ofAdd χ') = ∏ i, sH i (Multiplicative.ofAdd (e χ' i))` using `by conv_lhs => rw [hχ]`. Rewrite using `[ofAdd_sum, map_prod]`. Both sides reduce to the same expression.

Simplify using `only [NumD.torus_generator_apply, NumD.tor_b, N.cub.face₂, N.cub.face₃, _root_.mul_one, div_one]`. Use `congr 2`. Use `congr 1`. Rewrite using `[ht]`. Simplify using `only [MonoidHom.finset_prod_apply, MonoidHom.zpow_apply]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_prod, ofMul_zpow, ofMul_mul]`. Conclude with `(sum_sym_inv W C hBC fun i k => Additive.ofMul (sH k (Multiplicative.ofAdd (e χ' i)))).symm`.
-/
theorem tor_rel (hT : TensFacts W φ e wv) (hdet : IsUnit (W + W.transpose).det) (t' : Multiplicative N'.X →* Fˣ) :
    ∃ ts : Fin r → (Multiplicative N.X →* Fˣ), GtRelV W φ e wv (N'.tor t') fun j => N.tor (ts j) := by
  obtain ⟨hφm, -, hem, heb, -, -, -, -⟩ := hT
  have hBC : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  let E : N'.X ≃+ (Fin r → N.X) := AddEquiv.ofBijective (AddMonoidHom.mk' e fun a b => funext (hem a b)) heb
  let sH : Fin r → Multiplicative N.X →* Fˣ := fun k =>
    t'.comp (AddMonoidHom.toMultiplicative ((E.symm : (Fin r → N.X) →+ N'.X).comp (AddMonoidHom.single (fun _ : Fin r => N.X) k)))
  let C := (W + W.transpose)⁻¹
  refine ⟨fun j => ∏ k, sH k ^ C j k, fun j => ?_, fun χ' => ?_⟩
  · have h1 := hφm 1 1 j
    rw [_root_.mul_one] at h1
    exact mul_eq_left.1 h1.symm
  · have hχ : χ' = ∑ i, E.symm (Pi.single i (e χ' i)) := by
      rw [← map_sum, Finset.univ_sum_single]; exact (E.symm_apply_apply χ').symm
    have ht : t' (Multiplicative.ofAdd χ') = ∏ i, sH i (Multiplicative.ofAdd (e χ' i)) := by
      conv_lhs => rw [hχ]
      rw [ofAdd_sum, map_prod]
      rfl
    simp only [NumD.torus_generator_apply, NumD.tor_b, N.cub.face₂, N.cub.face₃, _root_.mul_one, div_one]
    congr 2
    congr 1
    rw [ht]
    simp only [MonoidHom.finset_prod_apply, MonoidHom.zpow_apply]
    apply Additive.ofMul.injective
    simp only [ofMul_prod, ofMul_zpow, ofMul_mul]
    exact (sum_sym_inv W C hBC fun i k => Additive.ofMul (sH k (Multiplicative.ofAdd (e χ' i)))).symm

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

/- English proof (translation)
Use `choose g hg using fun j => exists_gt_over N (φ v'.b j)`. Take `⟨u', hu'⟩` from `hex g`. Establish `hb : u'.b = v'.b` using `hT.2.1.1 (funext fun j => (hu'.1 j).trans (hg j))`. Take `⟨t', ht'⟩` from `(N'.exists_tor_iff (u'⁻¹ * v')).2 (by rw [NumD.Gt.mul_b, NumD.Gt.inv_b, hb, inv_mul_cancel])`. Take `⟨ts, hts⟩` from `tor_rel hT hdet t'`.

Establish `h` using `hmul u' (N'.tor t') g (fun j => N.tor (ts j)) hu' hts`. Rewrite `h` using `[ht', mul_inv_cancel_left]`. Conclude with `⟨_, h⟩`.
-/
theorem of_exist_mul (hT : TensFacts W φ e wv) (hdet : IsUnit (W + W.transpose).det)
    (hex : ∀ vs : Fin r → N.Gt, ∃ v' : N'.Gt, GtRelV W φ e wv v' vs)
    (hmul : ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us →
      GtRelV W φ e wv (v' * u') (vs * us))
    (v' : N'.Gt) : ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs := by
  choose g hg using fun j => exists_gt_over N (φ v'.b j)
  obtain ⟨u', hu'⟩ := hex g
  have hb : u'.b = v'.b := hT.2.1.1 (funext fun j => (hu'.1 j).trans (hg j))
  obtain ⟨t', ht'⟩ := (N'.exists_tor_iff (u'⁻¹ * v')).2 (by rw [NumD.Gt.mul_b, NumD.Gt.inv_b, hb, inv_mul_cancel])
  obtain ⟨ts, hts⟩ := tor_rel hT hdet t'
  have h := hmul u' (N'.tor t') g (fun j => N.tor (ts j)) hu' hts
  rw [ht', mul_inv_cancel_left] at h
  exact ⟨_, h⟩

end GlobalTheory.Mum.TensTor.Vonto
