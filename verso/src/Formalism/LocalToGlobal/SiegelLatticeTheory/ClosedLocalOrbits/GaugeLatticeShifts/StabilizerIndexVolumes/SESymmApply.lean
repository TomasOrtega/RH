import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StClosed

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
  {ι : Type} [Fintype ι] [DecidableEq ι]

def gramOf (g : ι → S.V) : Matrix ι ι E := fun k l => S.hT (g k) (g l)

def coordL (g : ι → S.V) (k : ι) : S.V →ₗ[E] E := ∑ l, ((gramOf g)⁻¹ k l) • S.hT (g l)

def cOf (g : ι → S.V) (v : S.V) : ι → E := fun k => coordL g k v

/- English proof (translation)
Use extensionality with `k`. Simplify using `[cOf, coordL, Matrix.mulVec, dotProduct, LinearMap.sum_apply]`.
-/
theorem cOf_eq (g : ι → S.V) (v : S.V) : cOf g v = (gramOf g)⁻¹ *ᵥ (fun l => S.hT (g l) v) := by
  ext k
  simp [cOf, coordL, Matrix.mulVec, dotProduct, LinearMap.sum_apply]

/- English proof (translation)
Use extensionality with `k`. Simplify using `[cOf]`.
-/
theorem cOf_add (g : ι → S.V) (v w : S.V) : cOf g (v + w) = cOf g v + cOf g w := by
  ext k; simp [cOf]

/- English proof (translation)
Use extensionality with `k`. Simplify using `[cOf]`.
-/
theorem cOf_smul (g : ι → S.V) (a : E) (v : S.V) : cOf g (a • v) = a • cOf g v := by
  ext k; simp [cOf]

/- English proof (translation)
Rewrite using `[cOf_eq]`. Establish `: (fun l => S.hT (g l) (g m)) = (gramOf g) *ᵥ (Pi.single m 1)`. Use extensionality with `l`. Simplify using `[gramOf, Matrix.mulVec_single]`. Rewrite using `[this, Matrix.mulVec_mulVec, nonsing_inv_mul _ hG, Matrix.one_mulVec]`.
-/
theorem cOf_g (g : ι → S.V) (hG : IsUnit (gramOf g).det) (m : ι) : cOf g (g m) = Pi.single m 1 := by
  rw [cOf_eq]
  have : (fun l => S.hT (g l) (g m)) = (gramOf g) *ᵥ (Pi.single m 1) := by
    ext l; simp [gramOf, Matrix.mulVec_single]
  rw [this, Matrix.mulVec_mulVec, nonsing_inv_mul _ hG, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[cOf_add]`. Use `congr 1`. Establish `: cOf g (∑ m, y m • g m) = ∑ m, y m • cOf g (g m)`. Use extensionality with `k`. Simplify using `[cOf, map_sum]`.

Rewrite using `[this]`. Simplify using `only [cOf_g g hG]`. Use extensionality with `k`. Simplify using `[Pi.single_apply]`.
-/
theorem cOf_comb (g : ι → S.V) (hG : IsUnit (gramOf g).det) (v : S.V) (y : ι → E) :
    cOf g (v + ∑ m, y m • g m) = cOf g v + y := by
  rw [cOf_add]
  congr 1
  have : cOf g (∑ m, y m • g m) = ∑ m, y m • cOf g (g m) := by
    ext k; simp [cOf, map_sum]
  rw [this]
  simp only [cOf_g g hG]
  ext k; simp [Pi.single_apply]

/- English proof (translation)
Rewrite using `[cOf_eq, Matrix.mulVec_mulVec, mul_nonsing_inv _ hG, Matrix.one_mulVec]`.
-/
theorem gram_cOf (g : ι → S.V) (hG : IsUnit (gramOf g).det) (v : S.V) :
    (gramOf g) *ᵥ cOf g v = fun l => S.hT (g l) v := by
  rw [cOf_eq, Matrix.mulVec_mulVec, mul_nonsing_inv _ hG, Matrix.one_mulVec]

def sL (g : ι → S.V) (X : Matrix ι ι E) : S.V →ₗ[E] S.V :=
  LinearMap.id + ∑ m, ∑ k, ((X - 1) m k) • (coordL g k).smulRight (g m)

/- English proof (translation)
Simplify using `only [sL, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul, cOf]`.
-/
theorem sL_apply (g : ι → S.V) (X : Matrix ι ι E) (v : S.V) :
    sL g X v = v + ∑ m, ((X - 1) *ᵥ cOf g v) m • g m := by
  simp only [sL, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul, cOf]

/- English proof (translation)
Rewrite using `[sL_apply, cOf_comb g hG, Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws.
-/
theorem cOf_sL (g : ι → S.V) (hG : IsUnit (gramOf g).det) (X : Matrix ι ι E) (v : S.V) :
    cOf g (sL g X v) = X *ᵥ cOf g v := by
  rw [sL_apply, cOf_comb g hG, Matrix.sub_mulVec, Matrix.one_mulVec]; abel

/- English proof (translation)
Rewrite using `[sL_apply g X, cOf_sL g hG, sL_apply g Y, sL_apply g (X * Y), add_assoc, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[← add_smul]`. Use `congr 1`.

Simplify using `only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sL_comp (g : ι → S.V) (hG : IsUnit (gramOf g).det) (X Y : Matrix ι ι E) (v : S.V) :
    sL g X (sL g Y v) = sL g (X * Y) v := by
  rw [sL_apply g X, cOf_sL g hG, sL_apply g Y, sL_apply g (X * Y), add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← add_smul]
  congr 1
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Pi.sub_apply]
  ring

/- English proof (translation)
Rewrite using `[sL_apply]`. Simplify using the standard rewrite rules.
-/
theorem sL_one (g : ι → S.V) (v : S.V) : sL g 1 v = v := by
  rw [sL_apply]; simp

def sE (g : ι → S.V) (hG : IsUnit (gramOf g).det) (X Y : Matrix ι ι E) (hXY : X * Y = 1) (hYX : Y * X = 1) :
    S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinearMap (sL g X) (sL g Y)
    (by ext v; simp only [LinearMap.comp_apply, LinearMap.id_apply]; rw [sL_comp g hG, hXY, sL_one])
    (by ext v; simp only [LinearMap.comp_apply, LinearMap.id_apply]; rw [sL_comp g hG, hYX, sL_one])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sE_apply (g : ι → S.V) (hG : IsUnit (gramOf g).det) (X Y : Matrix ι ι E) (hXY : X * Y = 1)
    (hYX : Y * X = 1) (v : S.V) : sE g hG X Y hXY hYX v = sL g X v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sE_symm_apply (g : ι → S.V) (hG : IsUnit (gramOf g).det) (X Y : Matrix ι ι E) (hXY : X * Y = 1)
    (hYX : Y * X = 1) (v : S.V) : (sE g hG X Y hXY hYX).symm v = sL g Y v := rfl

/- English proof (translation)
Use `S.herm.eq (g k) (g l)` as an intermediate fact. Simplify `this` using `[gramOf, starRingEnd_apply]`.
-/
theorem gram_herm (g : ι → S.V) (k l : ι) : star (gramOf g k l) = gramOf g l k := by
  have := S.herm.eq (g k) (g l)
  simpa [gramOf, starRingEnd_apply] using this

/- English proof (translation)
Establish `h1 : ∀ n, S.hT (g n) y = ((gramOf g) *ᵥ cOf g y) n` using `fun n => by rw [gram_cOf g hG]`. Establish `h2 : ∀ n, S.hT x (g n) = star (((gramOf g) *ᵥ cOf g x) n)` using `fun n => by`. Rewrite using `[gram_cOf g hG]`. Use `S.herm.eq (g n) x` as an intermediate fact. Simplify `this.symm` using `[starRingEnd_apply]`.

Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]`. Establish `hxB : S.hT x (∑ n, β n • g n) = star (cOf g x) ⬝ᵥ ((gramOf g) *ᵥ β)`. Simplify using `only [map_sum, LinearMap.map_smul, smul_eq_mul, h2]`. Simplify using `only [Matrix.mulVec, dotProduct, star_sum, star_mul', Pi.star_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[← gram_herm g n k]`. Expand and normalize the polynomial expressions, which then agree. Establish `hAy : S.hT (∑ m, α m • g m) y = star α ⬝ᵥ ((gramOf g) *ᵥ cOf g y)`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, h1]`.

Simplify using `[dotProduct]`. Establish `hAB : S.hT (∑ m, α m • g m) (∑ n, β n • g n) = star α ⬝ᵥ ((gramOf g) *ᵥ β)`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, dotProduct, Matrix.mulVec, Pi.star_apply, gramOf, Finset.mul_sum, RingHom.id_apply]`. Use `Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hxB, hAy, hAB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_comb (g : ι → S.V) (hG : IsUnit (gramOf g).det) (x y : S.V) (α β : ι → E) :
    S.hT (x + ∑ m, α m • g m) (y + ∑ n, β n • g n) =
      S.hT x y + star (cOf g x) ⬝ᵥ ((gramOf g) *ᵥ β) + star α ⬝ᵥ ((gramOf g) *ᵥ cOf g y) +
        star α ⬝ᵥ ((gramOf g) *ᵥ β) := by
  have h1 : ∀ n, S.hT (g n) y = ((gramOf g) *ᵥ cOf g y) n := fun n => by rw [gram_cOf g hG]
  have h2 : ∀ n, S.hT x (g n) = star (((gramOf g) *ᵥ cOf g x) n) := fun n => by
    rw [gram_cOf g hG]
    have := S.herm.eq (g n) x
    simpa [starRingEnd_apply] using this.symm
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
  have hxB : S.hT x (∑ n, β n • g n) = star (cOf g x) ⬝ᵥ ((gramOf g) *ᵥ β) := by
    simp only [map_sum, LinearMap.map_smul, smul_eq_mul, h2]
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n _ => ?_
    rw [← gram_herm g n k]; ring
  have hAy : S.hT (∑ m, α m • g m) y = star α ⬝ᵥ ((gramOf g) *ᵥ cOf g y) := by
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, h1]
    simp [dotProduct]
  have hAB : S.hT (∑ m, α m • g m) (∑ n, β n • g n) = star α ⬝ᵥ ((gramOf g) *ᵥ β) := by
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, dotProduct, Matrix.mulVec, Pi.star_apply, gramOf, Finset.mul_sum, RingHom.id_apply]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_)
    ring
  rw [hxB, hAy, hAB]
  ring

/- English proof (translation)
Rewrite using `[sL_apply, sL_apply, hT_comb g hG]`. Use `set p := cOf g x`. Use `set q := cOf g y`. Establish `key : star (X *ᵥ p) ⬝ᵥ ((gramOf g) *ᵥ (X *ᵥ q)) = star p ⬝ᵥ ((gramOf g) *ᵥ q)`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX]`.

Simplify using `only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, star_sub]`. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sL_isom (g : ι → S.V) (hG : IsUnit (gramOf g).det) (X : Matrix ι ι E)
    (hX : X.conjTranspose * gramOf g * X = gramOf g) (x y : S.V) :
    S.hT (sL g X x) (sL g X y) = S.hT x y := by
  rw [sL_apply, sL_apply, hT_comb g hG]
  set p := cOf g x
  set q := cOf g y
  have key : star (X *ᵥ p) ⬝ᵥ ((gramOf g) *ᵥ (X *ᵥ q)) = star p ⬝ᵥ ((gramOf g) *ᵥ q) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, dotProduct_sub,
    sub_dotProduct, star_sub]
  rw [key]
  ring

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
