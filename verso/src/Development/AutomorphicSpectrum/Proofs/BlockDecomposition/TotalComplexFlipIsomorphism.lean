import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.DCFlip

variable {R : Type} [CommRing R]

def sw (K : DCx.{w} R) (x : ∀ p q, K.X p q) : ∀ q p, K.flip.X q p :=
  fun q p => (-1 : ℤ) ^ (p * q) • x p q

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sw_apply (K : DCx.{w} R) (x : ∀ p q, K.X p q) (q p : ℕ) :
    sw K x q p = (-1 : ℤ) ^ (p * q) • x p q := rfl

/- English proof (translation)
Establish `hm : (-1 : ℤ) ^ m * (-1 : ℤ) ^ n = 1` using `by rw [← pow_add]; exact h.neg_one_pow`. Establish `hn : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1` using `by rw [← mul_pow]; simp`. Conclude with `mul_right_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℤ) ≠ 0)) (hm.trans hn.symm)`.
-/
theorem neg_one_pow_eq_of_even {m n : ℕ} (h : Even (m + n)) : (-1 : ℤ) ^ m = (-1 : ℤ) ^ n := by
  have hm : (-1 : ℤ) ^ m * (-1 : ℤ) ^ n = 1 := by rw [← pow_add]; exact h.neg_one_pow
  have hn : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by rw [← mul_pow]; simp
  exact mul_right_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℤ) ≠ 0)) (hm.trans hn.symm)

/- English proof (translation)
Rewrite using `[smul_smul, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem sign_smul_sign_smul {M : Type w} [AddCommGroup M] (k : ℕ) (z : M) :
    (-1 : ℤ) ^ k • (-1 : ℤ) ^ k • z = z := by
  rw [smul_smul, ← mul_pow]; simp

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Apply the tactic sequence `rcases a with _ | a <;> rcases b with _ | b`. Simplify using `[DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]`. Simplify using `[DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]`. Simplify using `[DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]`.

Establish `e1 : (-1 : ℤ) ^ ((b + 1) * a) = (-1 : ℤ) ^ ((b + 1) * (a + 1) + (b + 1))` using `neg_one_pow_eq_of_even ⟨(b + 1) * a + (b + 1), by ring⟩`. Establish `e2 : (-1 : ℤ) ^ (a + 1 + b * (a + 1)) = (-1 : ℤ) ^ ((b + 1) * (a + 1))`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply, map_zsmul, smul_add, smul_smul, ← pow_add]`.

Rewrite using `[e1, e2]`. Conclude with `add_comm _ _`.
-/
theorem D_sw (K : DCx.{w} R) (x : ∀ p q, K.X p q) : K.flip.D (sw K x) = sw K (K.D x) := by
  funext a b
  rcases a with _ | a <;> rcases b with _ | b
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]
  · have e1 : (-1 : ℤ) ^ ((b + 1) * a) = (-1 : ℤ) ^ ((b + 1) * (a + 1) + (b + 1)) :=
      neg_one_pow_eq_of_even ⟨(b + 1) * a + (b + 1), by ring⟩
    have e2 : (-1 : ℤ) ^ (a + 1 + b * (a + 1)) = (-1 : ℤ) ^ ((b + 1) * (a + 1)) := by
      congr 1; ring
    simp only [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply, map_zsmul, smul_add, smul_smul, ← pow_add]
    rw [e1, e2]
    exact add_comm _ _

def swHom (K : DCx.{w} R) : Cx.Hom K.tot K.flip.tot (RingHom.id R) where
  f n :=
    { toFun := fun x => ⟨sw K x.1, fun q p h => by
        change (-1 : ℤ) ^ (p * q) • x.1 p q = 0
        rw [x.2 p q (by omega), smul_zero]⟩
      map_add' := fun x y => Subtype.ext (funext fun q => funext fun p =>
        smul_add ((-1 : ℤ) ^ (p * q)) (x.1 p q) (y.1 p q))
      map_smul' := fun c x => Subtype.ext (funext fun q => funext fun p =>
        smul_comm ((-1 : ℤ) ^ (p * q)) c (x.1 p q)) }
  comm n x := Subtype.ext (D_sw K x.1)

/- English proof (translation)
Introduce `R _ K`. Use `⟨swHom K, fun n => ⟨fun x y h => ?_, fun y => ?_⟩, fun n x p q => rfl⟩` and prove the remaining obligations. Use `Subtype.ext (funext fun p => funext fun q => ?_)` and prove the remaining obligations. Establish `h' : (-1 : ℤ) ^ (p * q) • x.1 p q = (-1 : ℤ) ^ (p * q) • y.1 p q` using `congrFun (congrFun (congrArg Subtype.val h) q) p`. Establish `h''` using `congrArg (fun z => (-1 : ℤ) ^ (p * q) • z) h'`.

Simplify `h''` using `only [sign_smul_sign_smul]`. Use `⟨⟨fun p q => (-1 : ℤ) ^ (p * q) • y.1 q p, fun p q h => ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(-1 : ℤ) ^ (p * q) • y.1 q p = 0`. Rewrite using `[y.2 q p (by omega), smul_zero]`. Use `Subtype.ext (funext fun q => funext fun p => ?_)` and prove the remaining obligations.

Conclude with `sign_smul_sign_smul (p * q) (y.1 q p)`.
-/
theorem flip_tot : ∀ {R : Type} [CommRing R] (K : DCx.{w} R), ∃ φ : Cx.Hom K.tot K.flip.tot (RingHom.id R), (∀ n, Function.Bijective (φ.f n)) ∧ ∀ n (x : K.tot.X n) p q, (φ.f n x).1 q p = (-1 : ℤ) ^ (p * q) • x.1 p q := by
  intro R _ K
  refine ⟨swHom K, fun n => ⟨fun x y h => ?_, fun y => ?_⟩, fun n x p q => rfl⟩
  · refine Subtype.ext (funext fun p => funext fun q => ?_)
    have h' : (-1 : ℤ) ^ (p * q) • x.1 p q = (-1 : ℤ) ^ (p * q) • y.1 p q :=
      congrFun (congrFun (congrArg Subtype.val h) q) p
    have h'' := congrArg (fun z => (-1 : ℤ) ^ (p * q) • z) h'
    simpa only [sign_smul_sign_smul] using h''
  · refine ⟨⟨fun p q => (-1 : ℤ) ^ (p * q) • y.1 q p, fun p q h => ?_⟩, ?_⟩
    · change (-1 : ℤ) ^ (p * q) • y.1 q p = 0
      rw [y.2 q p (by omega), smul_zero]
    · refine Subtype.ext (funext fun q => funext fun p => ?_)
      exact sign_smul_sign_smul (p * q) (y.1 q p)

end GlobalTheory.CompanionTheory.DCFlip
