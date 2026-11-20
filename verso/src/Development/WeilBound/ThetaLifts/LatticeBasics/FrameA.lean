import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtArch

noncomputable section

namespace GlobalTheory.ThK.Dbl.Frame

open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

section Generic

variable {S β : Type} [CommRing S] [Fintype β] [DecidableEq β]

def two : GL β S →* GL (β ⊕ β) S :=
  MonoidHom.mk' (fun g => ⟨fromBlocks g.1 0 0 g.1, fromBlocks (g⁻¹).1 0 0 (g⁻¹).1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩) fun _ _ => Units.ext (by simp [fromBlocks_multiply])

def wit (a : S) (T : GL β S) : GL (β ⊕ β) S :=
  have h : fromBlocks ((1 - a) • 1) (a • 1) (T⁻¹).1 (-(T⁻¹).1) * fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1) = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.neg_mul, Units.inv_mul]
    refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> module
  ⟨_, _, mul_eq_one_comm.1 h, h⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `fromBlocks g.1 0 0 g.1 * fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1) * _ = _`. Use `Eq.trans ?_ (fromRows_mul 1 1 g.1).symm` and prove the remaining obligations. Simplify using `[fromBlocks_multiply, fromBlocks_mul_fromRows]`.
-/
theorem frame_diag (g T : GL β S) (a : S) : (two g * wit a T).1 * (fromRows 1 0 : Matrix (β ⊕ β) β S) = diagCols β * g.1 := by
  change fromBlocks g.1 0 0 g.1 * fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1) * _ = _
  refine Eq.trans ?_ (fromRows_mul 1 1 g.1).symm
  simp [fromBlocks_multiply, fromBlocks_mul_fromRows]

omit [DecidableEq β] in
/- English proof (translation)
Establish `mm : (g.map c).map c = g` using `Matrix.ext fun i j => hc _`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, mm, transpose_mul, transpose_mul, hJ, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem gram_sym (c : S →+* S) (hc : ∀ z, c (c z) = z) {ε : S} {J : Matrix β β S} (hJ : (J.map c)ᵀ = ε • J) (g : Matrix β β S) :
    ((gᵀ * J * g.map c).map c)ᵀ = ε • (gᵀ * J * g.map c) := by
  have mm : (g.map c).map c = g := Matrix.ext fun i j => hc _
  rw [Matrix.map_mul, Matrix.map_mul, mm, transpose_mul, transpose_mul, hJ, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rfl

/- English proof (translation)
Establish `mm : ∀ X : Matrix β β S, (X.map c).map c = X` using `fun X => Matrix.ext fun i j => hc _`. Use `set G := g.1ᵀ * J * g.1.map c with hG`. Establish `h1 : (G.map c)ᵀ = ε • G` using `gram_sym c hc hJ _`. Establish `h2 : T.1ᵀ * G = ε • 1`. Use `congrArg (fun X : Matrix β β S => ε • (X.map c)ᵀ) hT` as an intermediate fact.

Simplify `this` using `only [Matrix.map_mul (M := T.1.map c), mm, transpose_mul, h1, Matrix.mul_smul, smul_smul, hε, one_smul, Matrix.map_one _ (map_zero c) (map_one c), transpose_one]`. Establish `h3 : (two g).1ᵀ * dbl J * (two g).1.map c = dbl G`. Express the relevant statement in the definitionally equal form `(fromBlocks g.1 0 0 g.1)ᵀ * _ * (fromBlocks g.1 0 0 g.1).map c = _`. Simplify using `[dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, hG]`. Establish `h4 : (wit a T).1.map c = fromBlocks 1 ((1 - a) • T.1.map c) 1 (-a • T.1.map c)`.

Establish `e : c a = 1 - a` using `by rw [← ha]; ring`. Express the relevant statement in the definitionally equal form `(fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1)).map c = _`. Rewrite using `[fromBlocks_map, Matrix.map_one _ (map_zero c) (map_one c)]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp [e]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Units.val_mul, transpose_mul, Matrix.map_mul, Matrix.mul_assoc]`. Use `_ = _ := by`. Rewrite using `[h3, h4, Matrix.mul_assoc]`. Express the relevant statement in the definitionally equal form `(fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1))ᵀ * _ = _`. Simplify using `only [dbl, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.zero_mul, smul_zero, add_zero, zero_add, transpose_smul, transpose_one, hT, h2]`.

Apply the tactic sequence `refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> module`.
-/
theorem frame_gram (c : S →+* S) (hc : ∀ z, c (c z) = z) {ε a : S} (hε : ε * ε = 1) (ha : a + c a = 1) {J : Matrix β β S}
    (hJ : (J.map c)ᵀ = ε • J) (g T : GL β S) (hT : g.1ᵀ * J * g.1.map c * T.1.map c = 1) :
    (two g * wit a T).1ᵀ * dbl J * (two g * wit a T).1.map c = fromBlocks 0 1 (ε • 1) 0 := by
  have mm : ∀ X : Matrix β β S, (X.map c).map c = X := fun X => Matrix.ext fun i j => hc _
  set G := g.1ᵀ * J * g.1.map c with hG
  have h1 : (G.map c)ᵀ = ε • G := gram_sym c hc hJ _
  have h2 : T.1ᵀ * G = ε • 1 := by
    have := congrArg (fun X : Matrix β β S => ε • (X.map c)ᵀ) hT
    simpa only [Matrix.map_mul (M := T.1.map c), mm, transpose_mul, h1, Matrix.mul_smul, smul_smul, hε, one_smul,
      Matrix.map_one _ (map_zero c) (map_one c), transpose_one] using this
  have h3 : (two g).1ᵀ * dbl J * (two g).1.map c = dbl G := by
    change (fromBlocks g.1 0 0 g.1)ᵀ * _ * (fromBlocks g.1 0 0 g.1).map c = _
    simp [dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, hG]
  have h4 : (wit a T).1.map c = fromBlocks 1 ((1 - a) • T.1.map c) 1 (-a • T.1.map c) := by
    have e : c a = 1 - a := by rw [← ha]; ring
    change (fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1)).map c = _
    rw [fromBlocks_map, Matrix.map_one _ (map_zero c) (map_one c)]
    congr 1 <;> ext i j <;> simp [e]
  calc _ = (wit a T).1ᵀ * ((two g).1ᵀ * dbl J * (two g).1.map c) * (wit a T).1.map c := by
        simp only [Units.val_mul, transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [h3, h4, Matrix.mul_assoc]
        change (fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1))ᵀ * _ = _
        simp only [dbl, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          Matrix.neg_mul, Matrix.mul_neg, Matrix.zero_mul, smul_zero, add_zero, zero_add, transpose_smul, transpose_one, hT, h2]
        refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> module

def Int (A : Subring S) {m : Type} (X : Matrix m m S) : Prop := ∀ i j, X i j ∈ A

omit [DecidableEq β] in
/- English proof (translation)
Introduce `_ _` and use `sum_mem fun _ _ => mul_mem (h _ _) (h' _ _)`.
-/
theorem Int.mul {A : Subring S} {X Y : Matrix β β S} (h : Int A X) (h' : Int A Y) : Int A (X * Y) :=
  fun _ _ => sum_mem fun _ _ => mul_mem (h _ _) (h' _ _)

/- English proof (translation)
Establish `o : Int A (1 : Matrix β β S)` using `fun i j => by rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]`. Apply the tactic sequence `constructor <;> rintro (i | i) (j | j)`. Use `exacts [o i j, mul_mem ha (h i j), o i j, mul_mem (sub_mem ha (one_mem _)) (h i j), mul_mem (sub_mem (one_mem _) ha) (o i j), mul_mem ha (o i j), h' i j, neg_mem (h' i j)]`.
-/
theorem int_wit {A : Subring S} {a : S} (ha : a ∈ A) {T : GL β S} (h : Int A T.1) (h' : Int A (T⁻¹).1) :
    Int A (wit a T).1 ∧ Int A ((wit a T)⁻¹).1 := by
  have o : Int A (1 : Matrix β β S) := fun i j => by rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
  constructor <;> rintro (i | i) (j | j)
  exacts [o i j, mul_mem ha (h i j), o i j, mul_mem (sub_mem ha (one_mem _)) (h i j),
    mul_mem (sub_mem (one_mem _) ha) (o i j), mul_mem ha (o i j), h' i j, neg_mem (h' i j)]

/- English proof (translation)
Establish `e : (two a).1 = l.1 • (two g).1`. Express the relevant statement in the definitionally equal form `fromBlocks _ _ _ _ = l.1 • fromBlocks _ _ _ _`. Simplify using `[fromBlocks_smul, hl]`. Establish `e1 : (two a)⁻¹ * x * two a = (two g)⁻¹ * x * two g`. Establish `: ∀ y : GL (β ⊕ β) S, two a * ((two g)⁻¹ * y * two g) = y * two a` using `fun y => Units.ext <| by`.

Simplify using `only [Units.val_mul, e, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Rewrite using `[mul_assoc, ← this, inv_mul_cancel_left]`. Rewrite using `[e1]`. Use `⟨fun k => ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[show (two g * w)⁻¹ * x * (two g * w) = w⁻¹ * ((two g)⁻¹ * x * two g) * w by group]`.

Conclude with `(h'.mul k).mul h`. Rewrite using `[show (two g)⁻¹ * x * two g = w * ((two g * w)⁻¹ * x * (two g * w)) * w⁻¹ by group]`. Conclude with `(h.mul k).mul h'`.
-/
theorem int_conj {A : Subring S} {a g : GL β S} {l : Sˣ} (hl : a.1 = l.1 • g.1) {w : GL (β ⊕ β) S} (h : Int A w.1)
    (h' : Int A (w⁻¹).1) (x : GL (β ⊕ β) S) :
    Int A ((two a)⁻¹ * x * two a).1 ↔ Int A ((two g * w)⁻¹ * x * (two g * w)).1 := by
  have e : (two a).1 = l.1 • (two g).1 := by
    change fromBlocks _ _ _ _ = l.1 • fromBlocks _ _ _ _
    simp [fromBlocks_smul, hl]
  have e1 : (two a)⁻¹ * x * two a = (two g)⁻¹ * x * two g := by
    have : ∀ y : GL (β ⊕ β) S, two a * ((two g)⁻¹ * y * two g) = y * two a := fun y => Units.ext <| by
      simp only [Units.val_mul, e, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  rw [e1]
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [show (two g * w)⁻¹ * x * (two g * w) = w⁻¹ * ((two g)⁻¹ * x * two g) * w by group]
    exact (h'.mul k).mul h
  · rw [show (two g)⁻¹ * x * two g = w * ((two g * w)⁻¹ * x * (two g * w)) * w⁻¹ by group]
    exact (h.mul k).mul h'

end Generic

/- English proof (translation)
Take `⟨g, ε, s, hs, h1, h2⟩` from `Hgt.exists_cartan_frame hM hd h two_ne_zero`. Establish `c0 : c ≠ 0` using `right_ne_zero_of_mul_eq_one hc`. Use `⟨g, fun T hT x hx => mul_eq_one_comm.trans (Hgt.unitary_iff_commute (Q := (dbl J)ᵀ) (mul_ne_zero hs c0) ?_ _ x ?_ ?_)⟩` and prove the remaining obligations. Establish `: IsUnit J.det`. Use `(isUnit_iff_isUnit_det _).1 hd` as an intermediate fact.

Rewrite `this` using `[det_smul]`. Conclude with `isUnit_of_mul_isUnit_right this`. Rewrite using `[isUnit_iff_isUnit_det, det_transpose, dbl, det_fromBlocks_zero₂₁, det_neg]`. Conclude with `this.mul ((isUnit_one.neg.pow _).mul this)`. Use `set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => if ε i then 1 else -1 with hD`.

Establish `dd : D * D = 1`. Rewrite using `[hD, diagonal_mul_diagonal, ← diagonal_one]`. Apply the tactic sequence `congr 1; funext i; split_ifs <;> simp`. Establish `dh : Dᴴ = D`. Rewrite using `[hD, diagonal_conjTranspose]`.

Apply the tactic sequence `congr 1; funext i; simp only [Pi.star_apply]; split_ifs <;> simp`. Establish `e1 : T.1ᴴ * D = (2 * c) • 1`. Use `congrArg transpose hT` as an intermediate fact. Rewrite `this` using `[transpose_mul, transpose_mul, transpose_mul, transpose_one, transpose_transpose]`. Rewrite using `[← h1, ← this]`.

Simplify using `only [transpose_smul, smul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Complex.ofReal_ofNat]`. Both sides reduce to the same expression. Establish `e2 : T.1ᴴ = (2 * c) • D` using `by rw [← Matrix.mul_one T.1ᴴ, ← dd, ← Matrix.mul_assoc, e1, Matrix.smul_mul, Matrix.one_mul]`. Establish `e3 : T.1ᴴ * T.1 = (4 : ℂ) • 1`. Establish `: T.1 = (2 * star c) • D` using `by rw [← conjTranspose_conjTranspose T.1, e2, conjTranspose_smul, dh]; simp`.

Rewrite using `[e2, this, Matrix.smul_mul, Matrix.mul_smul, dd, smul_smul]`. Use `congr 1`. Take the linear combination `4 * hc`. Establish `e4 : g.1ᴴ * ((s * c) • (Jᵀ * θ)) * g.1 = (2⁻¹ : ℂ) • 1`. Rewrite using `[← h2]`.

Simplify using `only [transpose_smul, smul_smul, Matrix.mul_smul, Matrix.smul_mul, Complex.ofReal_ofNat]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e5 : (two g).1ᴴ * ((s * c) • ((dbl J)ᵀ * fromBlocks θ 0 0 (-θ))) * (two g).1 = (2⁻¹ : ℂ) • 1`. Express the relevant statement in the definitionally equal form `(fromBlocks g.1 0 0 g.1)ᴴ * _ * fromBlocks g.1 0 0 g.1 = _`.

Rewrite using `[← fromBlocks_one, fromBlocks_smul, ← e4]`. Simplify using `[dbl, fromBlocks_transpose, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_smul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Units.val_mul, conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = 1 := by`.

Rewrite using `[e5, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Express the relevant statement in the definitionally equal form `_ • ((fromBlocks 1 ((2⁻¹ : ℂ) • T.1) 1 ((2⁻¹ - 1 : ℂ) • T.1))ᴴ * fromBlocks 1 ((2⁻¹ : ℂ) • T.1) 1 ((2⁻¹ - 1 : ℂ) • T.1)) = _`. Rewrite using `[← fromBlocks_one (l := Fin n) (m := Fin n)]`. Simplify using `only [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_smul, conjTranspose_smul, conjTranspose_one, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, e3, star_sub, star_inv₀, star_ofNat, star_one]`. Apply the tactic sequence `refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> module`.

Use `congrArg transpose hx` as an intermediate fact. Rewrite `this` using `[transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc]`. Conclude with `this`.
-/
theorem exists_arch {n : ℕ} {J θ : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hc : star c * c = 1) (hM : (c • J)ᴴ = c • J) (hd : IsUnit (c • J))
    (h : IsCartan (c • J) θ) : ∃ g : GL (Fin n) ℂ, ∀ T : GL (Fin n) ℂ, g.1ᵀ * J * g.1.map star * T.1.map star = 1 →
      ∀ x : GL (Fin n ⊕ Fin n) ℂ, x.1ᵀ * dbl J * x.1.map star = dbl J →
        (((two g * wit 2⁻¹ T)⁻¹ * x * (two g * wit 2⁻¹ T)).1 * ((two g * wit 2⁻¹ T)⁻¹ * x * (two g * wit 2⁻¹ T)).1ᴴ = 1 ↔
          Commute x.1 (fromBlocks θ 0 0 (-θ))) := by
  obtain ⟨g, ε, s, hs, h1, h2⟩ := Hgt.exists_cartan_frame hM hd h two_ne_zero
  have c0 : c ≠ 0 := right_ne_zero_of_mul_eq_one hc
  refine ⟨g, fun T hT x hx => mul_eq_one_comm.trans (Hgt.unitary_iff_commute (Q := (dbl J)ᵀ) (mul_ne_zero hs c0) ?_ _ x ?_ ?_)⟩
  · have : IsUnit J.det := by
      have := (isUnit_iff_isUnit_det _).1 hd
      rw [det_smul] at this
      exact isUnit_of_mul_isUnit_right this
    rw [isUnit_iff_isUnit_det, det_transpose, dbl, det_fromBlocks_zero₂₁, det_neg]
    exact this.mul ((isUnit_one.neg.pow _).mul this)
  · set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => if ε i then 1 else -1 with hD
    have dd : D * D = 1 := by
      rw [hD, diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext i; split_ifs <;> simp
    have dh : Dᴴ = D := by
      rw [hD, diagonal_conjTranspose]
      congr 1; funext i; simp only [Pi.star_apply]; split_ifs <;> simp
    have e1 : T.1ᴴ * D = (2 * c) • 1 := by
      have := congrArg transpose hT
      rw [transpose_mul, transpose_mul, transpose_mul, transpose_one, transpose_transpose] at this
      rw [← h1, ← this]
      simp only [transpose_smul, smul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Complex.ofReal_ofNat]
      rfl
    have e2 : T.1ᴴ = (2 * c) • D := by rw [← Matrix.mul_one T.1ᴴ, ← dd, ← Matrix.mul_assoc, e1, Matrix.smul_mul, Matrix.one_mul]
    have e3 : T.1ᴴ * T.1 = (4 : ℂ) • 1 := by
      have : T.1 = (2 * star c) • D := by rw [← conjTranspose_conjTranspose T.1, e2, conjTranspose_smul, dh]; simp
      rw [e2, this, Matrix.smul_mul, Matrix.mul_smul, dd, smul_smul]
      congr 1
      linear_combination 4 * hc
    have e4 : g.1ᴴ * ((s * c) • (Jᵀ * θ)) * g.1 = (2⁻¹ : ℂ) • 1 := by
      rw [← h2]
      simp only [transpose_smul, smul_smul, Matrix.mul_smul, Matrix.smul_mul, Complex.ofReal_ofNat]
      congr 1
      ring
    have e5 : (two g).1ᴴ * ((s * c) • ((dbl J)ᵀ * fromBlocks θ 0 0 (-θ))) * (two g).1 = (2⁻¹ : ℂ) • 1 := by
      change (fromBlocks g.1 0 0 g.1)ᴴ * _ * fromBlocks g.1 0 0 g.1 = _
      rw [← fromBlocks_one, fromBlocks_smul, ← e4]
      simp [dbl, fromBlocks_transpose, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_smul]
    calc _ = (wit 2⁻¹ T).1ᴴ * ((two g).1ᴴ * ((s * c) • ((dbl J)ᵀ * fromBlocks θ 0 0 (-θ))) * (two g).1) * (wit 2⁻¹ T).1 := by
          simp only [Units.val_mul, conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [e5, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
          change _ • ((fromBlocks 1 ((2⁻¹ : ℂ) • T.1) 1 ((2⁻¹ - 1 : ℂ) • T.1))ᴴ * fromBlocks 1 ((2⁻¹ : ℂ) • T.1) 1 ((2⁻¹ - 1 : ℂ) • T.1)) = _
          rw [← fromBlocks_one (l := Fin n) (m := Fin n)]
          simp only [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_smul, conjTranspose_smul, conjTranspose_one, Matrix.mul_one,
            Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, e3, star_sub, star_inv₀, star_ofNat, star_one]
          refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> module
  · have := congrArg transpose hx
    rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
    exact this

end GlobalTheory.ThK.Dbl.Frame

end
