import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingProperties
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.PairVal

/- English proof (translation)
Simplify using `[cubN, Finset.prod_range_succ]`.
-/
theorem cubN_succ {A U : Type} [CommGroup A] [CommGroup U] (θ : A → A → A → U) (k : ℕ) (m x : A) :
    cubN θ (k + 1) 1 m x = cubN θ k 1 m x * θ (m ^ k) m x := by
  simp [cubN, Finset.prod_range_succ]

/- English proof (translation)
Use `h 1 1 j` as an intermediate fact. Rewrite `this` using `[_root_.one_mul]`. Conclude with `mul_eq_left.1 this.symm`.
-/
theorem comp_one {B C : Type} [CommGroup B] [CommGroup C] {r : ℕ} {φ : B → Fin r → C}
    (h : ∀ x y j, φ (x * y) j = φ x j * φ y j) (j : Fin r) : φ 1 j = 1 := by
  have := h 1 1 j
  rw [_root_.one_mul] at this
  exact mul_eq_left.1 this.symm

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [comp_one h]`. Consider the case `succ m ih => rw [pow_succ, h, ih, pow_succ]`.
-/
theorem comp_pow {B C : Type} [CommGroup B] [CommGroup C] {r : ℕ} {φ : B → Fin r → C}
    (h : ∀ x y j, φ (x * y) j = φ x j * φ y j) (x : B) (m : ℕ) (j : Fin r) : φ (x ^ m) j = φ x j ^ m := by
  induction m with
  | zero => simp [comp_one h]
  | succ m ih => rw [pow_succ, h, ih, pow_succ]

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [cubN, mul_comm]`. Consider the case `succ k ih`. Establish `h` using `hc (b ^ k) b a`. Simplify using `only [comp_pow hφ, ← mul_pow] at h`.

Establish `split : ∀ P p Q q R s : Fˣ, P * p / (Q * q * (R * s)) = P / (Q * R) * (p / (q * s))`. Introduce `P p Q q R s`. Rewrite using `[_root_.mul_mul_mul_comm, div_mul_div_comm]`. Simplify using `only [cubN_succ, split, mul_zpow, Finset.prod_mul_distrib, pow_succ]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `ih'` using `congrArg Additive.ofMul ih`. Establish `h'` using `congrArg Additive.ofMul h`. Simplify using `only [ofMul_mul, ofMul_pow] at ih' h' ⊢`. Take the linear combination `(norm := abel) ih' + h'`.
-/
theorem cube_prod (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (U : N'.A → Fˣ)
    (hφ : ∀ x y j, φ (x * y) j = φ x j * φ y j)
    (hc : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u =
      (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) *
      U (x * y) * U (x * u) * U (y * u) * U 1) (k : ℕ) (b a : N'.A) :
    cubN N'.θ k 1 b a * U (b ^ k * a) * U 1 * (U b * U a) ^ k =
      (∏ i, ∏ j, (cubN N.θ k 1 (φ b i * φ b j) (φ a i * φ a j) /
        (cubN N.θ k 1 (φ b i) (φ a i) * cubN N.θ k 1 (φ b j) (φ a j))) ^ W i j) *
      U (b ^ k) * U a * (U (b * a) * U 1) ^ k := by
  induction k with
  | zero => simp [cubN, mul_comm]
  | succ k ih =>
    have h := hc (b ^ k) b a
    simp only [comp_pow hφ, ← mul_pow] at h
    have split : ∀ P p Q q R s : Fˣ, P * p / (Q * q * (R * s)) = P / (Q * R) * (p / (q * s)) := by
      intro P p Q q R s
      rw [_root_.mul_mul_mul_comm, div_mul_div_comm]
    simp only [cubN_succ, split, mul_zpow, Finset.prod_mul_distrib, pow_succ]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_mul, ofMul_pow] at ih' h' ⊢
    linear_combination (norm := abel) ih' + h'

/- English proof (translation)
Rewrite using `[NumD.Gt.mul_s, N.c_add]`. Establish `m1` using `g.mult z z'`. Establish `m2` using `g'.mult z z'`. Establish `co` using `N.cub.coc (N.c z) (N.c z') g'.b g.b`. Rewrite `co` using `[N.cub.s12 (N.c z * N.c z') g'.b g.b]`.

Rewrite using `[N.cub.s12 (N.c z') g'.b (N.c z), N.cub.s01 (N.c z') (N.c z), N.cub.s12 (N.c z) g.b]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Use `replace m1 := congrArg Additive.ofMul m1`. Use `replace m2 := congrArg Additive.ofMul m2`. Use `replace co := congrArg Additive.ofMul co`.

Simplify using `only [ofMul_mul, ofMul_div] at m1 m2 co ⊢`. Take the linear combination `(norm := abel) -m1 - m2 + co`.
-/
theorem torusExtensionPair_correction_eq_value_quotient (N : NumD F) (g g' : N.Gt) (z z' : N.X) (C C₁ C₂ : Fˣ) :
    g'.s z * g.s z' / (N.θ (N.c z') g'.b (N.c z) * N.θ (N.c z') g'.b g.b * N.θ (N.c z) g.b (N.c z' * g'.b)) *
      (C / (C₁ * C₂)) = (g * g').s (z + z') * C / (g.s z * C₁ * (g'.s z' * C₂)) := by
  rw [NumD.Gt.mul_s, N.c_add]
  have m1 := g.mult z z'
  have m2 := g'.mult z z'
  have co := N.cub.coc (N.c z) (N.c z') g'.b g.b
  rw [N.cub.s12 (N.c z * N.c z') g'.b g.b] at co
  rw [N.cub.s12 (N.c z') g'.b (N.c z), N.cub.s01 (N.c z') (N.c z), N.cub.s12 (N.c z) g.b]
  apply Additive.ofMul.injective
  replace m1 := congrArg Additive.ofMul m1
  replace m2 := congrArg Additive.ofMul m2
  replace co := congrArg Additive.ofMul co
  simp only [ofMul_mul, ofMul_div] at m1 m2 co ⊢
  linear_combination (norm := abel) -m1 - m2 + co

end GlobalTheory.Mum.TensTor.PairVal

namespace GlobalTheory.Mum.TensTor.PairVal

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

/- English proof (translation)
Take `⟨hφ, -, -, -, -, -, hcube, -⟩` from `hT`. Establish `hcU : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u = (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) / (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) * U (x * y) * U (x * u) * U (y * u) * U 1`. Introduce `x y u`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, ← hU]`.

Conclude with `hcube x y u`. Establish `hA` using `cube_prod W φ U hφ hcU k p'.1.2.b q'.1.2.b`. Simplify using `only [hp.2.1, hq.2.1] at hA`. Establish `hG` using `hq.2.2 p'.1.1.toAdd`. Simplify using `only [hU, ← Units.val_mul] at hG`.

Use `replace hG := Units.ext hG`. Simplify using `only [hp.1, hq.2.1, ← N'.QT_pow_b p'] at hG`. Establish `hX : ∀ i j, N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) = (qs j).1.2.s (ps i).1.1.toAdd * (qs i).1.2.s (ps j).1.1.toAdd / (N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (N.c (ps i).1.1.toAdd) * N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (qs i).1.2.b * N.θ …` using `fun i j => (torusExtensionPair_correction_eq_value_quotient N (qs i).1.2 (qs j).1.2 (ps i).1.1.toAdd (ps j).1.1.toAdd _ _ _).symm`. Simplify using `only [hX, mul_zpow, Finset.prod_mul_distrib]`. Rewrite using `[NumD.tk]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `hA'` using `congrArg Additive.ofMul hA`. Establish `hG'` using `congrArg Additive.ofMul hG`. Simplify using `only [ofMul_mul, ofMul_pow] at hA' hG' ⊢`. Take the linear combination `(norm := abel) hA' + hG'`.
-/
theorem tk_tens (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (hT : TensFacts W φ e wv) (U : N'.A → Fˣ) (hU : ∀ x, wv x = (U x : F)) {k : ℕ} (q' p' : N'.QT k)
    (qs ps : Fin r → N.QT k) (hq : QRelV W φ e wv q' qs) (hp : QRelV W φ e wv p' ps) :
    N'.tk q' p' * (U p'.1.2.b * U q'.1.2.b) ^ k =
      (∏ i, ∏ j, (N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j))) ^ W i j) *
      (U (p'.1.2.b * q'.1.2.b) * U 1) ^ k := by
  obtain ⟨hφ, -, -, -, -, -, hcube, -⟩ := hT
  have hcU : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u =
      (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) *
      U (x * y) * U (x * u) * U (y * u) * U 1 := by
    intro x y u
    apply Units.ext
    simp only [Units.val_mul, ← hU]
    exact hcube x y u
  have hA := cube_prod W φ U hφ hcU k p'.1.2.b q'.1.2.b
  simp only [hp.2.1, hq.2.1] at hA
  have hG := hq.2.2 p'.1.1.toAdd
  simp only [hU, ← Units.val_mul] at hG
  replace hG := Units.ext hG
  simp only [hp.1, hq.2.1, ← N'.QT_pow_b p'] at hG
  have hX : ∀ i j, N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) =
      (qs j).1.2.s (ps i).1.1.toAdd * (qs i).1.2.s (ps j).1.1.toAdd /
        (N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (N.c (ps i).1.1.toAdd) *
          N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (qs i).1.2.b *
          N.θ (N.c (ps i).1.1.toAdd) (qs i).1.2.b (N.c (ps j).1.1.toAdd * (qs j).1.2.b)) *
      (cubN N.θ k 1 ((ps i).1.2.b * (ps j).1.2.b) ((qs i).1.2.b * (qs j).1.2.b) /
        (cubN N.θ k 1 (ps i).1.2.b (qs i).1.2.b * cubN N.θ k 1 (ps j).1.2.b (qs j).1.2.b)) :=
    fun i j => (torusExtensionPair_correction_eq_value_quotient N (qs i).1.2 (qs j).1.2 (ps i).1.1.toAdd (ps j).1.1.toAdd _ _ _).symm
  simp only [hX, mul_zpow, Finset.prod_mul_distrib]
  rw [NumD.tk]
  apply Additive.ofMul.injective
  have hA' := congrArg Additive.ofMul hA
  have hG' := congrArg Additive.ofMul hG
  simp only [ofMul_mul, ofMul_pow] at hA' hG' ⊢
  linear_combination (norm := abel) hA' + hG'

/- English proof (translation)
Introduce `F _ N N' r W φ e wv hT k _ q' p' qs ps hq hp`. Set `U : N'.A → Fˣ` to `fun x => Units.mk0 (wv x) (hT.2.2.2.2.2.1 x)`. Establish `hU : ∀ x, wv x = (U x : F)` using `fun x => rfl`. Establish `h1` using `tk_tens W φ e wv hT U hU q' p' qs ps hq hp`. Establish `h2` using `tk_tens W φ e wv hT U hU p' q' ps qs hp hq`.

Rewrite `h2` using `[mul_comm q'.1.2.b p'.1.2.b]`. Establish `hper : ∀ i j, N.wp (qs i) (ps j) * N.wp (qs j) (ps i) = N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) / (N.tk (ps i * ps j) (qs i * qs j) / (N.tk (ps i) (qs i) * N.tk (ps j) (qs j)))`. Introduce `i j`. Establish `e1` using `WpPairing.wp_mul_left N (qs i) (qs j) (ps i * ps j)`. Establish `e2` using `WpPairing.wp_mul_right N (qs i) (ps i) (ps j)`.

Establish `e3` using `WpPairing.wp_mul_right N (qs j) (ps i) (ps j)`. Simplify using `only [NumD.wp] at e1 e2 e3 ⊢`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Use `replace e1 := congrArg Additive.ofMul e1`. Use `replace e2 := congrArg Additive.ofMul e2`.

Use `replace e3 := congrArg Additive.ofMul e3`. Simplify using `only [ofMul_mul, ofMul_div] at e1 e2 e3 ⊢`. Take the linear combination `(norm := abel) -e1 - e2 - e3`. Establish `hR : ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j = ∏ i, ∏ j, (N.wp (qs i) (ps j) * N.wp (qs j) (ps i)) ^ W i j`. Simplify using `only [Matrix.add_apply, Matrix.transpose_apply, zpow_add, Finset.prod_mul_distrib, mul_zpow]`.

Use `congr 1`. Rewrite using `[Finset.prod_comm]`. Establish `hD : ∀ f g : Fin r → Fin r → Fˣ, ∏ i, ∏ j, (f i j / g i j) ^ W i j = (∏ i, ∏ j, f i j ^ W i j) / ∏ i, ∏ j, g i j ^ W i j`. Introduce `f g`. Simplify using `only [div_zpow, Finset.prod_div_distrib]`.

Rewrite using `[hR]`. Simplify using `only [hper]`. Rewrite using `[hD]`. Rewrite using `[NumD.wp]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `h1'` using `congrArg Additive.ofMul h1`. Establish `h2'` using `congrArg Additive.ofMul h2`. Simplify using `only [ofMul_mul, ofMul_pow, ofMul_div] at h1' h2' ⊢`. Take the linear combination `(norm := abel) h1' - h2'`.
-/
theorem wp_eq_prod : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (k : ℕ), 1 ≤ k → ∀ (q' p' : N'.QT k) (qs ps : Fin r → N.QT k), QRelV W φ e wv q' qs → QRelV W φ e wv p' ps → N'.wp q' p' = ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j := by
  intro F _ N N' r W φ e wv hT k _ q' p' qs ps hq hp
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hT.2.2.2.2.2.1 x)
  have hU : ∀ x, wv x = (U x : F) := fun x => rfl
  have h1 := tk_tens W φ e wv hT U hU q' p' qs ps hq hp
  have h2 := tk_tens W φ e wv hT U hU p' q' ps qs hp hq
  rw [mul_comm q'.1.2.b p'.1.2.b] at h2
  have hper : ∀ i j, N.wp (qs i) (ps j) * N.wp (qs j) (ps i) =
      N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) /
        (N.tk (ps i * ps j) (qs i * qs j) / (N.tk (ps i) (qs i) * N.tk (ps j) (qs j))) := by
    intro i j
    have e1 := WpPairing.wp_mul_left N (qs i) (qs j) (ps i * ps j)
    have e2 := WpPairing.wp_mul_right N (qs i) (ps i) (ps j)
    have e3 := WpPairing.wp_mul_right N (qs j) (ps i) (ps j)
    simp only [NumD.wp] at e1 e2 e3 ⊢
    apply Additive.ofMul.injective
    replace e1 := congrArg Additive.ofMul e1
    replace e2 := congrArg Additive.ofMul e2
    replace e3 := congrArg Additive.ofMul e3
    simp only [ofMul_mul, ofMul_div] at e1 e2 e3 ⊢
    linear_combination (norm := abel) -e1 - e2 - e3
  have hR : ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j =
      ∏ i, ∏ j, (N.wp (qs i) (ps j) * N.wp (qs j) (ps i)) ^ W i j := by
    simp only [Matrix.add_apply, Matrix.transpose_apply, zpow_add, Finset.prod_mul_distrib, mul_zpow]
    congr 1
    rw [Finset.prod_comm]
  have hD : ∀ f g : Fin r → Fin r → Fˣ, ∏ i, ∏ j, (f i j / g i j) ^ W i j =
      (∏ i, ∏ j, f i j ^ W i j) / ∏ i, ∏ j, g i j ^ W i j := by
    intro f g
    simp only [div_zpow, Finset.prod_div_distrib]
  rw [hR]
  simp only [hper]
  rw [hD]
  rw [NumD.wp]
  apply Additive.ofMul.injective
  have h1' := congrArg Additive.ofMul h1
  have h2' := congrArg Additive.ofMul h2
  simp only [ofMul_mul, ofMul_pow, ofMul_div] at h1' h2' ⊢
  linear_combination (norm := abel) h1' - h2'

end GlobalTheory.Mum.TensTor.PairVal
