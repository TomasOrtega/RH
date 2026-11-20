import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfPowEqOne

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HtGen GlobalTheory.HalfGeo
open MonObj

namespace GlobalTheory.WeilHomGen

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Use `haveI : NeZero q := ⟨hq⟩`. Use `choose f hf using fun m t => (hex (e t) (s m) (he t) (hs m)).exists`. Establish `hfm : ∀ m t t', f m (t * t') = f m t * f m t'` using `fun m t t' => (hex (e (t * t')) (s m) (he _) (hs m)).unique (hf m _) (by`. Rewrite using `[map_mul]`. Conclude with `hmul _ _ _ _ _ (hf m t) (hf m t'))`.

Set `χ : Fin N → (T →* Kˣ)` to `fun m => MonoidHom.mk' (f m) (hfm m)`. Use `⟨χ, hf, fun χ' => ?_⟩` and prove the remaining obligations. Use `choose σ hσ using fun m => hsurj (s m) (hs m)`. Establish `hχσ : ∀ m k, χ m (σ k) = ζ ^ B k m` using `fun m k => (hex (s k) (s m) (hs k) (hs m)).unique (hσ k ▸ hf m (σ k)) (hG k m)`. Establish `hr : ∀ k, ∃ r : ℤ, ζ ^ r = χ' (σ k)` using `fun k => by`.

Establish `h1 : σ k ^ q = 1` using `hinj (by rw [map_pow, he, map_one])`. Establish `h2 : χ' (σ k) ∈ rootsOfUnity q K`. Rewrite using `[mem_rootsOfUnity, ← map_pow, h1, map_one]`. Rewrite `h2` using `[← hζ.zpowers_eq]`. Conclude with `h2`.

Use `choose r hr using hr`. Set `v : Fin N → ℤ` to `B⁻¹.mulVec r`. Establish `hv : B.mulVec v = r`. Simplify using `only [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hB, Matrix.one_mulVec]`. Establish `hq' : (q : ℤ) ≠ 0` using `by exact_mod_cast hq`.

Use `⟨fun m => (v m % q).toNat, ?_⟩` and prove the remaining obligations. Establish `key : ∀ k, χ' (σ k) = (∏ m, χ m ^ (v m % q).toNat) (σ k)` using `fun k => by`. Rewrite using `[← hr k, ← congrFun hv k, MonoidHom.finsetProd_apply]`. Establish `s` using `map_prod (zpowersHom Kˣ ζ) (fun m => Multiplicative.ofAdd (B k m * v m)) Finset.univ`. Rewrite `s` using `[← ofAdd_sum]`.

Use `s.trans (Finset.prod_congr rfl fun m _ => ?_)` and prove the remaining obligations. Establish `hz : (ζ ^ B k m) ^ q = 1`. Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]`. Rewrite using `[MonoidHom.pow_apply, hχσ, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hq'), ← zpow_eq_zpow_emod' _ hz, ← zpow_mul]`. Both sides reduce to the same expression.

Use `MonoidHom.ext fun t => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `hgen (e t) (he t)`. Establish `ht : t = ∏ m, σ m ^ n m` using `hinj (by`. Rewrite using `[hn, map_prod]`. Conclude with `Finset.prod_congr rfl fun m _ => by rw [map_pow, hσ])`.

Rewrite using `[ht, map_prod, map_prod]`. Conclude with `Finset.prod_congr rfl fun m _ => by rw [map_pow, map_pow, key]`.
-/
theorem exists_chars {G T K : Type} [CommGroup G] [CommGroup T] [Field K] {q : ℕ} (hq : q ≠ 0) (R : G → G → Kˣ → Prop)
    (hex : ∀ x y, x ^ q = 1 → y ^ q = 1 → ∃! c, R x y c)
    (hmul : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c'))
    (e : T →* G) (he : ∀ t, e t ^ q = 1) (hinj : Function.Injective e) (hsurj : ∀ g, g ^ q = 1 → ∃ t, e t = g)
    {N : ℕ} (s : Fin N → G) (ζ : Kˣ) (B : Matrix (Fin N) (Fin N) ℤ) (hζ : IsPrimitiveRoot ζ q) (hB : IsUnit B.det)
    (hs : ∀ m, s m ^ q = 1) (hG : ∀ m m', R (s m) (s m') (ζ ^ B m m'))
    (hgen : ∀ a : G, a ^ q = 1 → ∃ n : Fin N → ℕ, a = ∏ m, s m ^ n m) :
    ∃ χ : Fin N → (T →* Kˣ), (∀ m t, R (e t) (s m) (χ m t)) ∧
      ∀ χ' : T →* Kˣ, ∃ n : Fin N → ℕ, χ' = ∏ m, χ m ^ n m := by
  classical
  haveI : NeZero q := ⟨hq⟩
  choose f hf using fun m t => (hex (e t) (s m) (he t) (hs m)).exists
  have hfm : ∀ m t t', f m (t * t') = f m t * f m t' := fun m t t' =>
    (hex (e (t * t')) (s m) (he _) (hs m)).unique (hf m _) (by
      rw [map_mul]; exact hmul _ _ _ _ _ (hf m t) (hf m t'))
  let χ : Fin N → (T →* Kˣ) := fun m => MonoidHom.mk' (f m) (hfm m)
  refine ⟨χ, hf, fun χ' => ?_⟩
  choose σ hσ using fun m => hsurj (s m) (hs m)
  have hχσ : ∀ m k, χ m (σ k) = ζ ^ B k m := fun m k =>
    (hex (s k) (s m) (hs k) (hs m)).unique (hσ k ▸ hf m (σ k)) (hG k m)
  have hr : ∀ k, ∃ r : ℤ, ζ ^ r = χ' (σ k) := fun k => by
    have h1 : σ k ^ q = 1 := hinj (by rw [map_pow, he, map_one])
    have h2 : χ' (σ k) ∈ rootsOfUnity q K := by
      rw [mem_rootsOfUnity, ← map_pow, h1, map_one]
    rw [← hζ.zpowers_eq] at h2
    exact h2
  choose r hr using hr
  let v : Fin N → ℤ := B⁻¹.mulVec r
  have hv : B.mulVec v = r := by
    simp only [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hB, Matrix.one_mulVec]
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq
  refine ⟨fun m => (v m % q).toNat, ?_⟩
  have key : ∀ k, χ' (σ k) = (∏ m, χ m ^ (v m % q).toNat) (σ k) := fun k => by
    rw [← hr k, ← congrFun hv k, MonoidHom.finsetProd_apply]
    have s := map_prod (zpowersHom Kˣ ζ) (fun m => Multiplicative.ofAdd (B k m * v m)) Finset.univ
    rw [← ofAdd_sum] at s
    refine s.trans (Finset.prod_congr rfl fun m _ => ?_)
    have hz : (ζ ^ B k m) ^ q = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [MonoidHom.pow_apply, hχσ, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hq'),
      ← zpow_eq_zpow_emod' _ hz, ← zpow_mul]
    rfl
  refine MonoidHom.ext fun t => ?_
  obtain ⟨n, hn⟩ := hgen (e t) (he t)
  have ht : t = ∏ m, σ m ^ n m := hinj (by
    rw [hn, map_prod]
    exact Finset.prod_congr rfl fun m _ => by rw [map_pow, hσ])
  rw [ht, map_prod, map_prod]
  exact Finset.prod_congr rfl fun m _ => by rw [map_pow, map_pow, key]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z K _ ξ₀ ξ hξ q hq N s ζ B hζ hB hG hgen`. Substitute `hξ` using the available equality. Take `⟨Φ, hΦ⟩` from `GlobalTheory.WeilTorsChar.exists_mulEquiv_points _ Z.t.G Z.oF.t.G Z.m.φ Z.m.cart (Over.mk ξ₀)`. Set `P` to `GlobalTheory.Obj.toPolAV Z.oF`. Set `e : TorsK Z.t (ξ₀ ≫ Z.j) q →* (Over.mk ξ₀ ⟶ Z.oF.t.G)` to `Φ.symm.toMonoidHom.comp (TorsK Z.t (ξ₀ ≫ Z.j) q).subtype`.

Establish `he : ∀ t, e t = Φ.symm t.1` using `fun _ => rfl`. Take `⟨χ, h₁, h₂⟩` from `exists_chars (K := K) hq (fun x y u => Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) x y (unitOn u)) (fun x y hx hy => by`. Take `⟨w, hw, hu⟩` from `GlobalTheory.LevelCompare.weil_existsUnique P q x y hx hy`. Take `⟨u, rfl⟩` from `GlobalTheory.Ex.Specialise.unitOn_bijective.2 w`. Conclude with `⟨u, hw, fun u' hu' => GlobalTheory.Ex.Specialise.unitOn_bijective.1 (hu _ hu')⟩)`.

Use the proof step `(fun x x' y u u' h h' => by`. Use `weilIs_mul_left GlobalTheory.allSixLaws.1.globalFns _ P q _ x x' y _ _ h h'` as an intermediate fact. Establish `e' : unitOn (u * u') = unitOn u * unitOn u'` using `map_mul (Units.map _) u u'`. Rewrite using `[e']`. Conclude with `this)`.

Use `e (fun t => by`. Establish `ht : t.1 ^ q = 1` using `t.2`. Rewrite using `[he]`. Conclude with `(map_pow Φ.symm _ _).symm.trans ((congrArg Φ.symm ht).trans (map_one _)))`. Use the proof step `(Φ.symm.injective.comp Subtype.val_injective)`.

Use the proof step `(fun g hg => ⟨⟨Φ g, (map_pow Φ _ _).symm.trans ((congrArg Φ hg).trans (map_one _))⟩, Φ.symm_apply_apply g⟩)`. Use `s ζ B hζ hB hG.1 hG.2 hgen`. Use `⟨χ, fun m k a ha => ?_, h₂⟩` and prove the remaining obligations. Establish `: a = e k`. Rewrite using `[he]`.

Use `(Φ.eq_symm_apply).2 (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Conclude with `(hΦ a).trans ha`. Rewrite using `[this]`. Conclude with `h₁ m k`.
-/
theorem homSt : HomSt := by
  intro E _ _ _ H Dw l Xo c O _ β Z K _ ξ₀ ξ hξ q hq N s ζ B hζ hB hG hgen
  subst hξ
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.WeilTorsChar.exists_mulEquiv_points _ Z.t.G Z.oF.t.G Z.m.φ Z.m.cart (Over.mk ξ₀)
  let P := GlobalTheory.Obj.toPolAV Z.oF
  let e : TorsK Z.t (ξ₀ ≫ Z.j) q →* (Over.mk ξ₀ ⟶ Z.oF.t.G) :=
    Φ.symm.toMonoidHom.comp (TorsK Z.t (ξ₀ ≫ Z.j) q).subtype
  have he : ∀ t, e t = Φ.symm t.1 := fun _ => rfl
  obtain ⟨χ, h₁, h₂⟩ := exists_chars (K := K) hq
    (fun x y u => Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) x y (unitOn u))
    (fun x y hx hy => by
      obtain ⟨w, hw, hu⟩ := GlobalTheory.LevelCompare.weil_existsUnique P q x y hx hy
      obtain ⟨u, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 w
      exact ⟨u, hw, fun u' hu' => GlobalTheory.Ex.Specialise.unitOn_bijective.1 (hu _ hu')⟩)
    (fun x x' y u u' h h' => by
      have := weilIs_mul_left GlobalTheory.allSixLaws.1.globalFns _ P q _ x x' y _ _ h h'
      have e' : unitOn (u * u') = unitOn u * unitOn u' := map_mul (Units.map _) u u'
      rw [e']
      exact this)
    e (fun t => by
      have ht : t.1 ^ q = 1 := t.2
      rw [he]
      exact (map_pow Φ.symm _ _).symm.trans ((congrArg Φ.symm ht).trans (map_one _)))
    (Φ.symm.injective.comp Subtype.val_injective)
    (fun g hg => ⟨⟨Φ g, (map_pow Φ _ _).symm.trans ((congrArg Φ hg).trans (map_one _))⟩, Φ.symm_apply_apply g⟩)
    s ζ B hζ hB hG.1 hG.2 hgen
  refine ⟨χ, fun m k a ha => ?_, h₂⟩
  have : a = e k := by
    rw [he]
    refine (Φ.eq_symm_apply).2 (Over.OverMorphism.ext ?_)
    exact (hΦ a).trans ha
  rw [this]
  exact h₁ m k

end GlobalTheory.WeilHomGen
