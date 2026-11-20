import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Establish `hGn : G ^ n ≠ 0` using `pow_ne_zero n (left_ne_zero_of_mul hGc)`. Rewrite using `[mul_pow, mul_pow, mul_inv, show A * (G' ^ m * c' ^ m) * ((G ^ n)⁻¹ * (c ^ n)⁻¹) = A * G' ^ m * (G ^ n)⁻¹ * (c' ^ m * (c ^ n)⁻¹) by ring, h, mul_comm (G ^ n) B, mul_inv_cancel_right₀ hGn]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma mul_mul_pow_mul_inv_pow_eq {A B G G' c c' : ℂ} (m n : ℕ) (h : A * G' ^ m = G ^ n * B)
    (hGc : G * c ≠ 0) : A * (G' * c') ^ m * ((G * c) ^ n)⁻¹ = B * c' ^ m * (c ^ n)⁻¹ := by
  have hGn : G ^ n ≠ 0 := pow_ne_zero n (left_ne_zero_of_mul hGc)
  rw [mul_pow, mul_pow, mul_inv,
    show A * (G' ^ m * c' ^ m) * ((G ^ n)⁻¹ * (c ^ n)⁻¹) = A * G' ^ m * (G ^ n)⁻¹ * (c' ^ m * (c ^ n)⁻¹) by ring,
    h, mul_comm (G ^ n) B, mul_inv_cancel_right₀ hGn]
  ring

/- English proof (translation)
Substitute `ha ha'` using the available equality. Rewrite using `[mul_pow, mul_pow, mul_pow, mul_pow, hE]`. Clear the denominators using the available nonvanishing facts.
-/
private lemma mul_pow_mul_inv_pow_eq_of_factor {s a b a' b' x x' E E' : ℂ} (m n : ℕ) (ha : a = x * E * b)
    (ha' : a' = x' * E' * b') (hE : E' ^ m = E ^ n) (hx : x ≠ 0) (hx' : x' ≠ 0) (hEne : E ≠ 0)
    (hb : b ≠ 0) (hb' : b' ≠ 0) :
    s * b' ^ m * (b ^ n)⁻¹ = x ^ n * (x' ^ m)⁻¹ * (s * a' ^ m * (a ^ n)⁻¹) := by
  subst ha ha'
  rw [mul_pow, mul_pow, mul_pow, mul_pow, hE]
  field_simp

open PullHermitian in

/- English proof (translation)
Introduce `A A' _ _ L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hΛ₀ hex m n hiso`. Establish `hH` using `hermForm_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hex m n hiso`. Take `⟨w, hw⟩` from `hiso`. Unfold `HolUnif.IsAH at hu hu'`. Use `u.discrete` as an intermediate fact.

Establish `hxf : ∀ z, (u'.ex (F z)).left = (u.ex z).left ≫ f.left` using `fun z => by rw [hex z]; rfl`. Set `φ : L.ι × L'.ι → (Fin g → ℂ) → ℂ` to `fun p z => valAt' (u.ex z).left _ (w.s (idx f.left m n p.1 p.2)).val * u'.fr p.2 (F z) ^ m * (u.fr p.1 z ^ n)⁻¹`. Set `V : L.ι × L'.ι → Set (Fin g → ℂ)` to `fun p => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1 ∧ ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U p.2}`. Establish `hFc : Continuous F` using `LinearMap.continuous_of_finiteDimensional F`. Establish `hV : ∀ p, IsOpen (V p)` using `fun p => (u.hol (L.U p.1) 0).1.inter ((u'.hol (L'.U p.2) 0).1.preimage hFc)`.

Establish `hcov : ∀ z, ∃ p, z ∈ V p` using `fun z => by`. Take `⟨i, hi⟩` from `exists_chart (u.ex z).left hL`. Take `⟨j, hj⟩` from `exists_chart (u'.ex (F z)).left hL'`. Conclude with `⟨(i, j), hi, hj⟩`. Establish `hdiv : ∀ i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (lbPow L n) (lbPow (L'.pull f.left) m)).U (idx f.left m n i j)` using `fun i j z hi hj => idx_chart _ f.left m n i j hi (by rw [← hxf]; exact hj)`.

Establish `hφd : ∀ p, DifferentiableOn ℂ (φ p) (V p)` using `fun p => by`. Establish `h1` using `((u.hol _ (w.s (idx f.left m n p.1 p.2)).val).2).mono (fun z (hz : z ∈ V p) => hdiv p.1 p.2 z hz.1 hz.2)`. Establish `h2 : DifferentiableOn ℂ (fun z => u'.fr p.2 (F z)) (V p)` using `(u'.fr_hol p.2).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn (fun z hz => hz.2)`. Establish `h3 : DifferentiableOn ℂ (fun z => u.fr p.1 z) (V p)` using `(u.fr_hol p.1).mono (fun z hz => hz.1)`. Conclude with `(h1.mul (h2.pow m)).mul ((h3.pow n).inv fun z hz => pow_ne_zero _ (u.fr_ne _ z hz.1))`.

Establish `hagree : ∀ p q z, z ∈ V p → z ∈ V q → φ p z = φ q z`. Introduce and unpack `⟨i, j⟩ ⟨i', j'⟩ z ⟨hi, hj⟩ ⟨hi', hj'⟩`. Establish `hj₁ : ⊤ ≤ ((u.ex z).left ≫ f.left) ⁻¹ᵁ L'.U j` using `by rw [← hxf]; exact hj`. Establish `hj₁' : ⊤ ≤ ((u.ex z).left ≫ f.left) ⁻¹ᵁ L'.U j'` using `by rw [← hxf]; exact hj'`. Establish `hval` using `val_iso_pow (u.ex z).left f.left m n w hw i i' j j' hi hi' hj₁ hj₁'`.

Establish `hc` using `u.fr_compat i i' z (inf_of _ hi hi')`. Establish `hc'` using `u'.fr_compat j j' (F z) (inf_of _ hj hj')`. Rewrite `hc'` using `[hxf]`. Establish `hne : u.fr i z ≠ 0` using `u.fr_ne i z hi`. Simplify using `only [φ]`.

Rewrite `hne`, the goal using `[hc]`. Rewrite using `[hc']`. Conclude with `mul_mul_pow_mul_inv_pow_eq m n hval hne`. Take `⟨r, hr, hrφ⟩` from `exists_glue V hV hcov φ hφd hagree`. Establish `hφne : ∀ i j z, z ∈ V (i, j) → φ (i, j) z ≠ 0`.

Introduce `i j z hz`. Establish `hd` using `hdiv i j z hz.1 hz.2`. Simplify using `only [φ]`. Rewrite using `[valAt'_eq_unitVal _ hd]`. Conclude with `mul_ne_zero (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (u'.fr_ne j _ hz.2))) (inv_ne_zero (pow_ne_zero _ (u.fr_ne i z hz.1)))`.

Establish `hr_ne : ∀ z, r z ≠ 0` using `fun z => by`. Take `⟨⟨i, j⟩, hp⟩` from `hcov z`. Rewrite using `[hrφ _ z hp]`. Conclude with `hφne i j z hp`. Establish `hexl : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z` using `fun l z => by`.

Rewrite using `[u.ex_add, (u.ker _).2 l.2, _root_.mul_one]`. Establish `hexl' : ∀ (l : u.Λ) z, u'.ex (F (z + l)) = u'.ex (F z)` using `fun l z => by`. Rewrite using `[map_add, u'.ex_add, (u'.ker _).2 (hΛ₀ _ l.2), _root_.mul_one]`. Establish `hχne : ∀ l, χ l ≠ 0` using `fun l h0 => by simpa [h0] using hu.2.2.1 l`. Establish `hχne' : ∀ l, χ' l ≠ 0` using `fun l h0 => by simpa [h0] using hu'.2.2.1 l`.

Set `c : u.Λ → ℂ` to `fun l => χ l ^ n * (χ' ⟨F l, hΛ₀ l l.2⟩ ^ m)⁻¹`. Establish `h0 : ∀ a b : Fin g → ℂ, hermForm (0 : Matrix (Fin g) (Fin g) ℂ) a b = 0` using `fun a b => by`. Simplify using `[hermForm]`. Establish `hper : ∀ (l : u.Λ) z, r (z + l) = c l * Complex.exp (Real.pi * hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z (l : Fin g → ℂ) + Real.pi / 2 * hermForm (0 : Matrix (Fin g) (Fin g) ℂ) (l : Fin g → ℂ) (l : Fin g → ℂ)) * r z`. Introduce `l z`.

Simplify using `only [h0, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one]`. Take `⟨⟨i, j⟩, hp⟩` from `hcov z`. Establish `hzl : z + l ∈ V (i, j)` using `⟨by rw [hexl]; exact hp.1, by rw [hexl']; exact hp.2⟩`. Rewrite using `[hrφ _ _ hzl, hrφ _ _ hp]`. Establish `ha` using `hu.2.2.2 l i z hp.1`.

Establish `ha'` using `hu'.2.2.2 ⟨F l, hΛ₀ l l.2⟩ j (F z) hp.2`. Simplify using `only at ha'`. Establish `hb : u.fr i (z + l) ≠ 0` using `u.fr_ne i _ hzl.1`. Establish `hb' : u'.fr j (F z + F l) ≠ 0` using `u'.fr_ne j _ (by rw [← map_add]; exact hzl.2)`. Simplify using `only [φ, c]`.

Rewrite using `[hexl l z, map_add]`. Use `mul_pow_mul_inv_pow_eq_of_factor m n ha ha' ?_ (hχne l) (hχne' _) (Complex.exp_ne_zero _) hb hb'` and prove the remaining obligations. Rewrite using `[← Complex.exp_nat_mul, ← Complex.exp_nat_mul]`. Use `congr 1`. Establish `e1` using `hH z l`.

Establish `e2` using `hH l l`. Simplify using `only [hermForm] at e1 e2`. Take the linear combination `(Real.pi : ℂ) * e1 + ((Real.pi : ℂ) / 2) * e2`. Establish `hcn : ∀ l, ‖c l‖ = 1` using `fun l => by`. Simplify using `only [c, norm_mul, norm_inv, norm_pow, hu.2.2.1 l, hu'.2.2.1, one_pow, inv_one, _root_.mul_one]`.

Establish `key` using `(appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 c r Matrix.isHermitian_zero hcn hr hr_ne hper).2.1`. Introduce `l`. Establish `hl` using `key l`. Simplify using `only [c] at hl`. Conclude with `(mul_inv_eq_one₀ (pow_ne_zero _ (hχne' _))).1 hl`.
-/
theorem semicharacter_pull_eq_of_lbIso_pow :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB →
  ∀ (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ' : u'.Λ → ℂ), u.IsAH Hm χ → u'.IsAH Hm' χ' →
  ∀ (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hΛ₀ : ∀ l ∈ u.Λ, F l ∈ u'.Λ), (∀ z, u'.ex (F z) = u.ex z ≫ f) →
  ∀ m n : ℕ, LBIso (lbPow (L'.pull f.left) m) (lbPow L n) →
  ∀ l : u.Λ, χ l ^ n = χ' ⟨F l, hΛ₀ l l.2⟩ ^ m := by
  intro A A' _ _ L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hΛ₀ hex m n hiso

  have hH := hermForm_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hex m n hiso
  obtain ⟨w, hw⟩ := hiso
  unfold HolUnif.IsAH at hu hu'
  have := u.discrete
  have hxf : ∀ z, (u'.ex (F z)).left = (u.ex z).left ≫ f.left := fun z => by rw [hex z]; rfl

  let φ : L.ι × L'.ι → (Fin g → ℂ) → ℂ := fun p z =>
    valAt' (u.ex z).left _ (w.s (idx f.left m n p.1 p.2)).val * u'.fr p.2 (F z) ^ m * (u.fr p.1 z ^ n)⁻¹
  let V : L.ι × L'.ι → Set (Fin g → ℂ) := fun p =>
    {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1 ∧ ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U p.2}
  have hFc : Continuous F := LinearMap.continuous_of_finiteDimensional F
  have hV : ∀ p, IsOpen (V p) := fun p =>
    (u.hol (L.U p.1) 0).1.inter ((u'.hol (L'.U p.2) 0).1.preimage hFc)
  have hcov : ∀ z, ∃ p, z ∈ V p := fun z => by
    obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
    obtain ⟨j, hj⟩ := exists_chart (u'.ex (F z)).left hL'
    exact ⟨(i, j), hi, hj⟩
  have hdiv : ∀ i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U j →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (lbPow L n) (lbPow (L'.pull f.left) m)).U (idx f.left m n i j) :=
    fun i j z hi hj => idx_chart _ f.left m n i j hi (by rw [← hxf]; exact hj)
  have hφd : ∀ p, DifferentiableOn ℂ (φ p) (V p) := fun p => by
    have h1 := ((u.hol _ (w.s (idx f.left m n p.1 p.2)).val).2).mono
      (fun z (hz : z ∈ V p) => hdiv p.1 p.2 z hz.1 hz.2)
    have h2 : DifferentiableOn ℂ (fun z => u'.fr p.2 (F z)) (V p) :=
      (u'.fr_hol p.2).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn
        (fun z hz => hz.2)
    have h3 : DifferentiableOn ℂ (fun z => u.fr p.1 z) (V p) := (u.fr_hol p.1).mono (fun z hz => hz.1)
    exact (h1.mul (h2.pow m)).mul ((h3.pow n).inv fun z hz => pow_ne_zero _ (u.fr_ne _ z hz.1))
  have hagree : ∀ p q z, z ∈ V p → z ∈ V q → φ p z = φ q z := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ z ⟨hi, hj⟩ ⟨hi', hj'⟩
    have hj₁ : ⊤ ≤ ((u.ex z).left ≫ f.left) ⁻¹ᵁ L'.U j := by rw [← hxf]; exact hj
    have hj₁' : ⊤ ≤ ((u.ex z).left ≫ f.left) ⁻¹ᵁ L'.U j' := by rw [← hxf]; exact hj'
    have hval := val_iso_pow (u.ex z).left f.left m n w hw i i' j j' hi hi' hj₁ hj₁'
    have hc := u.fr_compat i i' z (inf_of _ hi hi')
    have hc' := u'.fr_compat j j' (F z) (inf_of _ hj hj')
    rw [hxf] at hc'
    have hne : u.fr i z ≠ 0 := u.fr_ne i z hi
    simp only [φ]
    rw [hc] at hne ⊢
    rw [hc']
    exact mul_mul_pow_mul_inv_pow_eq m n hval hne
  obtain ⟨r, hr, hrφ⟩ := exists_glue V hV hcov φ hφd hagree
  have hφne : ∀ i j z, z ∈ V (i, j) → φ (i, j) z ≠ 0 := by
    intro i j z hz
    have hd := hdiv i j z hz.1 hz.2
    simp only [φ]
    rw [valAt'_eq_unitVal _ hd]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (u'.fr_ne j _ hz.2)))
      (inv_ne_zero (pow_ne_zero _ (u.fr_ne i z hz.1)))
  have hr_ne : ∀ z, r z ≠ 0 := fun z => by
    obtain ⟨⟨i, j⟩, hp⟩ := hcov z
    rw [hrφ _ z hp]
    exact hφne i j z hp
  have hexl : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  have hexl' : ∀ (l : u.Λ) z, u'.ex (F (z + l)) = u'.ex (F z) := fun l z => by
    rw [map_add, u'.ex_add, (u'.ker _).2 (hΛ₀ _ l.2), _root_.mul_one]
  have hχne : ∀ l, χ l ≠ 0 := fun l h0 => by simpa [h0] using hu.2.2.1 l
  have hχne' : ∀ l, χ' l ≠ 0 := fun l h0 => by simpa [h0] using hu'.2.2.1 l
  let c : u.Λ → ℂ := fun l => χ l ^ n * (χ' ⟨F l, hΛ₀ l l.2⟩ ^ m)⁻¹
  have h0 : ∀ a b : Fin g → ℂ, hermForm (0 : Matrix (Fin g) (Fin g) ℂ) a b = 0 := fun a b => by
    simp [hermForm]
  have hper : ∀ (l : u.Λ) z, r (z + l) =
      c l * Complex.exp (Real.pi * hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z (l : Fin g → ℂ) +
        Real.pi / 2 * hermForm (0 : Matrix (Fin g) (Fin g) ℂ) (l : Fin g → ℂ) (l : Fin g → ℂ)) * r z := by
    intro l z
    simp only [h0, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one]
    obtain ⟨⟨i, j⟩, hp⟩ := hcov z
    have hzl : z + l ∈ V (i, j) := ⟨by rw [hexl]; exact hp.1, by rw [hexl']; exact hp.2⟩
    rw [hrφ _ _ hzl, hrφ _ _ hp]
    have ha := hu.2.2.2 l i z hp.1
    have ha' := hu'.2.2.2 ⟨F l, hΛ₀ l l.2⟩ j (F z) hp.2
    dsimp only at ha'
    have hb : u.fr i (z + l) ≠ 0 := u.fr_ne i _ hzl.1
    have hb' : u'.fr j (F z + F l) ≠ 0 := u'.fr_ne j _ (by rw [← map_add]; exact hzl.2)
    simp only [φ, c]
    rw [hexl l z, map_add]
    refine mul_pow_mul_inv_pow_eq_of_factor m n ha ha' ?_ (hχne l) (hχne' _) (Complex.exp_ne_zero _) hb hb'
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    have e1 := hH z l
    have e2 := hH l l
    simp only [hermForm] at e1 e2
    linear_combination (Real.pi : ℂ) * e1 + ((Real.pi : ℂ) / 2) * e2
  have hcn : ∀ l, ‖c l‖ = 1 := fun l => by
    simp only [c, norm_mul, norm_inv, norm_pow, hu.2.2.1 l, hu'.2.2.1, one_pow, inv_one, _root_.mul_one]
  have key := (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 c r
    Matrix.isHermitian_zero hcn hr hr_ne hper).2.1
  intro l
  have hl := key l
  simp only [c] at hl
  exact (mul_inv_eq_one₀ (pow_ne_zero _ (hχne' _))).1 hl

/- English proof (translation)
Introduce `A A' _ _ L L' g g' u u' Hm Hm' χ χ' f F hF n hn hL hL' hu hu' hex hiso`. Establish `hiso'` using `hiso.symm`. Use `⟨fun z w => ?_, semicharacter_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF hex n n hiso'⟩` and prove the remaining obligations. Establish `h` using `hermForm_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hex n n hiso' z w`. Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`.

Conclude with `(mul_left_cancel₀ hn' h).symm`.
-/
theorem appellHumbert_data_eq_of_lbIso_pow_pull :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ) (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (n : ℕ), 0 < n → L.IsLB → L'.IsLB → u.IsAH Hm χ → u'.IsAH Hm' χ' → (∀ z, u'.ex (F z) = u.ex z ≫ f) → LBIso (lbPow L n) (lbPow (L'.pull f.left) n) → (∀ z w, hermForm Hm z w = hermForm Hm' (F z) (F w)) ∧ ∀ l : u.Λ, χ l ^ n = χ' ⟨F l, hF l l.2⟩ ^ n := by
  intro A A' _ _ L L' g g' u u' Hm Hm' χ χ' f F hF n hn hL hL' hu hu' hex hiso
  have hiso' := hiso.symm
  refine ⟨fun z w => ?_,
    semicharacter_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF hex n n hiso'⟩
  have h := hermForm_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hex n n hiso' z w
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_left_cancel₀ hn' h).symm

end GlobalTheory
