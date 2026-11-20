import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityEighth

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns

open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms

section col

variable {A : Type*} [CommRing A] [StarRing A] {m : Type} [Fintype m] [DecidableEq m]

def colU : (m → A) ≃ Matrix m Unit A where
  toFun x := Matrix.of fun i _ => x i
  invFun X := fun i => X i ()
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, colU, Equiv.coe_fn_mk, Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))` and prove the remaining obligations. Use `show star (x i) * H i l * y l = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_col (H : Matrix m m A) (x y : m → A) (a b : Unit) :
    ((colU x)ᴴ * H * colU y) a b = star x ⬝ᵥ (H *ᵥ y) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, colU, Equiv.coe_fn_mk, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
  show star (x i) * H i l * y l = _
  ring

end col

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

abbrev fm {A : Type*} [CommRing A] [StarRing A] (H : Matrix m m A) (x y : m → A) : A :=
  star x ⬝ᵥ (H *ᵥ y)

/- English proof (translation)
Establish `hX : X = colU (fun i => X i ())`. Use extensionality with `i u`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h1` using `congrFun (congrFun h ()) ()`. Rewrite `h1` using `[hX, form_col]`. Conclude with `h1`. Introduce `h`. Use extensionality with `a b`.

Rewrite using `[hX, form_col]`. Conclude with `h`.
-/
private theorem conjTranspose_mul_mul_col_eq_const_iff_fm {A : Type*} [CommRing A] [StarRing A] (Hq : Matrix m m A) (t : A)
    (X : Matrix m Unit A) :
    Xᴴ * Hq * X = Matrix.of (fun _ _ => t) ↔ fm Hq (fun i => X i ()) (fun i => X i ()) = t := by
  have hX : X = colU (fun i => X i ()) := by
    ext i u
    rfl
  constructor
  · intro h
    have h1 := congrFun (congrFun h ()) ()
    rw [hX, form_col] at h1
    exact h1
  · intro h
    ext a b
    rw [hX, form_col]
    exact h

/- English proof (translation)
Establish `hF : IsFixF K F` using `Fact.out`. Take `⟨T, hTdef⟩ : ∃ T : Matrix Unit Unit (𝓞 K), T = Matrix.of (fun _ _ => ι n)` from `⟨_, rfl⟩`. Establish `hT : Tᴴ = T`. Rewrite using `[hTdef]`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.conjTranspose_apply, Matrix.of_apply]`. Rewrite using `[idealPowerSpanBounds.star_def]`. Conclude with `conjO_map hF n`. Establish `RC'' : ∀ X : Matrix m Unit (𝓞 K), (fun X => p' (fun i => X i ())) (X.map (mkk K 𝔭 k)) → (∀ a b, (Xᴴ * H * X - T) a b ∈ extP K 𝔭 ^ k) → ∀ S : Matrix Unit Unit (𝓞 K), (∀ a b, S a b ∈ extP K 𝔭 ^ k) → (∀ a b, (Sᴴ - S) a b ∈ extP K 𝔭 ^ (k + 1)) → ∃ Y : Matrix m Unit (𝓞 K), (∀ a b, Y a …`. Introduce `X hp hX S hS hS'`.

Establish `hXc : X = colU (fun i => X i ())`. Use extensionality with `i u`. Both sides reduce to the same expression. Establish `hx : fm H (fun i => X i ()) (fun i => X i ()) - ι n ∈ extP K 𝔭 ^ k`. Establish `h1` using `hX () ()`.

Rewrite `h1` using `[Matrix.sub_apply, hXc, form_col, hTdef, Matrix.of_apply]`. Conclude with `h1`. Take `⟨y, hy, hy'⟩` from `RC (fun i => X i ()) hp hx (S () ()) (hS () ()) (hS' () ())`. Use `⟨colU y, fun a b => hy a, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, Matrix.add_apply, hXc, form_col, form_col]`.

Conclude with `hy'`. Establish `h` using `card_rep_succ (m := m) (r := Unit) hK h𝔭 H hH T hT hj (fun X => p' (fun i => X i ())) (fun X Y hY => hinv (fun i => X i ()) (fun i => Y i ()) (fun a => hY a ())) RC''`. Establish `c1 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // p' (fun i => piQ K 𝔭 k (x i)) ∧ fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} = Nat.card {X : Matrix m Unit (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) // (fun X => p' (fun i => X i ())) (X.map (piQ K 𝔭 k)) ∧ Xᴴ * H.map (mkk K 𝔭 (k + …`. Rewrite using `[hTdef]`. Conclude with `Nat.card_congr (Equiv.subtypeEquiv colU (fun x => and_congr Iff.rfl (conjTranspose_mul_mul_col_eq_const_iff_fm (H.map (mkk K 𝔭 (k + 1))) (mkk K 𝔭 (k + 1) (ι n)) (colU x)).symm))`.

Establish `c2 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // p' x ∧ fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} = Nat.card {X : Matrix m Unit (𝓞 K ⧸ extP K 𝔭 ^ k) // (fun X => p' (fun i => X i ())) X ∧ Xᴴ * H.map (mkk K 𝔭 k) * X = T.map (mkk K 𝔭 k)}`. Rewrite using `[hTdef]`. Conclude with `Nat.card_congr (Equiv.subtypeEquiv colU (fun x => and_congr Iff.rfl (conjTranspose_mul_mul_col_eq_const_iff_fm (H.map (mkk K 𝔭 k)) (mkk K 𝔭 k (ι n)) (colU x)).symm))`. Rewrite using `[c1, c2]`. Simplify using `only [Fintype.card_unit, mul_one, pow_one] at h`.

Conclude with `h`.
-/
theorem card_vec_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (H : Matrix m m (𝓞 K)) (hH : Hᴴ = H) (n : 𝓞 F) {k j : ℕ}
    (hj : k + 1 ≤ 2 * j) (p' : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop)
    (hinv : ∀ x y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ j) →
      (p' (fun i => mkk K 𝔭 k ((x + y) i)) ↔ p' (fun i => mkk K 𝔭 k (x i))))
    (RC : ∀ x : m → 𝓞 K, p' (fun i => mkk K 𝔭 k (x i)) → fm H x x - ι n ∈ extP K 𝔭 ^ k →
      ∀ s ∈ extP K 𝔭 ^ k, star s - s ∈ extP K 𝔭 ^ (k + 1) →
      ∃ y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ j) ∧ fm H x y + fm H y x - s ∈ extP K 𝔭 ^ (k + 1)) :
    Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // p' (fun i => piQ K 𝔭 k (x i)) ∧
        fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} * Ideal.absNorm 𝔭 =
      Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) *
        Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // p' x ∧
          fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨T, hTdef⟩ : ∃ T : Matrix Unit Unit (𝓞 K), T = Matrix.of (fun _ _ => ι n) := ⟨_, rfl⟩
  have hT : Tᴴ = T := by
    rw [hTdef]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [idealPowerSpanBounds.star_def]
    exact conjO_map hF n
  have RC'' : ∀ X : Matrix m Unit (𝓞 K), (fun X => p' (fun i => X i ())) (X.map (mkk K 𝔭 k)) →
      (∀ a b, (Xᴴ * H * X - T) a b ∈ extP K 𝔭 ^ k) → ∀ S : Matrix Unit Unit (𝓞 K),
      (∀ a b, S a b ∈ extP K 𝔭 ^ k) → (∀ a b, (Sᴴ - S) a b ∈ extP K 𝔭 ^ (k + 1)) →
      ∃ Y : Matrix m Unit (𝓞 K), (∀ a b, Y a b ∈ extP K 𝔭 ^ j) ∧
        ∀ a b, (Xᴴ * H * Y + Yᴴ * H * X - S) a b ∈ extP K 𝔭 ^ (k + 1) := by
    intro X hp hX S hS hS'
    have hXc : X = colU (fun i => X i ()) := by
      ext i u
      rfl
    have hx : fm H (fun i => X i ()) (fun i => X i ()) - ι n ∈ extP K 𝔭 ^ k := by
      have h1 := hX () ()
      rw [Matrix.sub_apply, hXc, form_col, hTdef, Matrix.of_apply] at h1
      exact h1
    obtain ⟨y, hy, hy'⟩ := RC (fun i => X i ()) hp hx (S () ()) (hS () ()) (hS' () ())
    refine ⟨colU y, fun a b => hy a, fun a b => ?_⟩
    rw [Matrix.sub_apply, Matrix.add_apply, hXc, form_col, form_col]
    exact hy'
  have h := card_rep_succ (m := m) (r := Unit) hK h𝔭 H hH T hT hj (fun X => p' (fun i => X i ()))
    (fun X Y hY => hinv (fun i => X i ()) (fun i => Y i ()) (fun a => hY a ())) RC''
  have c1 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // p' (fun i => piQ K 𝔭 k (x i)) ∧
        fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} =
      Nat.card {X : Matrix m Unit (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) //
        (fun X => p' (fun i => X i ())) (X.map (piQ K 𝔭 k)) ∧
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X = T.map (mkk K 𝔭 (k + 1))} := by
    rw [hTdef]
    exact Nat.card_congr (Equiv.subtypeEquiv colU (fun x => and_congr Iff.rfl
      (conjTranspose_mul_mul_col_eq_const_iff_fm (H.map (mkk K 𝔭 (k + 1))) (mkk K 𝔭 (k + 1) (ι n)) (colU x)).symm))
  have c2 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // p' x ∧
        fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} =
      Nat.card {X : Matrix m Unit (𝓞 K ⧸ extP K 𝔭 ^ k) // (fun X => p' (fun i => X i ())) X ∧
        Xᴴ * H.map (mkk K 𝔭 k) * X = T.map (mkk K 𝔭 k)} := by
    rw [hTdef]
    exact Nat.card_congr (Equiv.subtypeEquiv colU (fun x => and_congr Iff.rfl
      (conjTranspose_mul_mul_col_eq_const_iff_fm (H.map (mkk K 𝔭 k)) (mkk K 𝔭 k (ι n)) (colU x)).symm))
  rw [c1, c2]
  simp only [Fintype.card_unit, mul_one, pow_one] at h
  exact h

section star

variable {A : Type*} [CommRing A] [StarRing A]

/- English proof (translation)
Use extensionality with `i`. Establish `hHij : ∀ j, star (H j i) = H i j` using `fun j => by`. Rewrite using `[← Matrix.conjTranspose_apply, hH]`. Simplify using `only [Matrix.mulVec, Matrix.vecMul, dotProduct, Pi.star_apply, star_sum, star_mul', star_star, hHij]`. Conclude with `Finset.sum_congr rfl (fun j _ => mul_comm _ _)`.
-/
theorem mulVec_eq_star {H : Matrix m m A} (hH : Hᴴ = H) (x : m → A) :
    H *ᵥ x = star (star x ᵥ* H) := by
  ext i
  have hHij : ∀ j, star (H j i) = H i j := fun j => by
    rw [← Matrix.conjTranspose_apply, hH]
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Pi.star_apply, star_sum, star_mul',
    star_star, hHij]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/- English proof (translation)
The claim follows from `Matrix.dotProduct_mulVec (star x) H y`.
-/
theorem fm_eq (H : Matrix m m A) (x y : m → A) : fm H x y = (star x ᵥ* H) ⬝ᵥ y := Matrix.dotProduct_mulVec (star x) H y

/- English proof (translation)
Establish `hHij : ∀ i j, star (H i j) = H j i` using `fun i j => by`. Rewrite using `[← Matrix.conjTranspose_apply, hH]`. Simplify using `only [fm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hHij, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fm_star {H : Matrix m m A} (hH : Hᴴ = H) (x y : m → A) : fm H y x = star (fm H x y) := by
  have hHij : ∀ i j, star (H i j) = H j i := fun i j => by
    rw [← Matrix.conjTranspose_apply, hH]
  simp only [fm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hHij,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/- English proof (translation)
Rewrite using `[Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]`.
-/
theorem vecMul_adjugate (H : Matrix m m A) (x : m → A) :
    (x ᵥ* H) ᵥ* H.adjugate = H.det • x := by
  rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]

/- English proof (translation)
Simplify using `only [Matrix.vecMul, dotProduct]`. Conclude with `Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_right _ _ (hw j))`.
-/
theorem vecMul_mem {J : Ideal A} {w : m → A} (hw : ∀ j, w j ∈ J) (M : Matrix m m A) (i : m) :
    (w ᵥ* M) i ∈ J := by
  simp only [Matrix.vecMul, dotProduct]
  exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_right _ _ (hw j))

end star

def Qc (𝔭 : Ideal (𝓞 F)) (k c : ℕ) (H : Matrix m m (𝓞 K)) (x : m → 𝓞 K ⧸ extP K 𝔭 ^ k) : Prop :=
  ∃ j, (star x ᵥ* H.map (mkk K 𝔭 k)) j ∉ idQ K 𝔭 k (c + 1)

/- English proof (translation)
Establish `e : ∀ j, (star (fun i => mkk K 𝔭 k (x i)) ᵥ* H.map (mkk K 𝔭 k)) j = mkk K 𝔭 k ((star x ᵥ* H) j)`. Introduce `j`. Establish `hs : star (fun i => mkk K 𝔭 k (x i)) = fun i => mkk K 𝔭 k (star x i)`. Use function extensionality and compare the values at `i`. Conclude with `idealPowerSpanBounds.star_mk 𝔭 k (x i)`.

Rewrite using `[hs]`. Conclude with `(RingHom.map_vecMul (mkk K 𝔭 k) H (star x) j).symm`. Unfold `Qc`. Simplify using `only [e, mk_mem_idQ hck]`.
-/
theorem Qc_mk {𝔭 : Ideal (𝓞 F)} {k c : ℕ} (hck : c + 1 ≤ k) (H : Matrix m m (𝓞 K)) (x : m → 𝓞 K) :
    Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i)) ↔ ∃ j, (star x ᵥ* H) j ∉ extP K 𝔭 ^ (c + 1) := by
  have e : ∀ j, (star (fun i => mkk K 𝔭 k (x i)) ᵥ* H.map (mkk K 𝔭 k)) j =
      mkk K 𝔭 k ((star x ᵥ* H) j) := by
    intro j
    have hs : star (fun i => mkk K 𝔭 k (x i)) = fun i => mkk K 𝔭 k (star x i) := by
      funext i
      exact idealPowerSpanBounds.star_mk 𝔭 k (x i)
    rw [hs]
    exact (RingHom.map_vecMul (mkk K 𝔭 k) H (star x) j).symm
  unfold Qc
  simp only [e, mk_mem_idQ hck]

/- English proof (translation)
Use `choose f hf using fun z : 𝓞 K ⧸ extP K 𝔭 ^ k => Ideal.Quotient.mk_surjective z`. Conclude with `⟨fun i => f (x i), funext fun i => hf _⟩`.
-/
theorem exists_liftv (𝔭 : Ideal (𝓞 F)) (k : ℕ) (x : m → 𝓞 K ⧸ extP K 𝔭 ^ k) :
    ∃ y : m → 𝓞 K, (fun i => mkk K 𝔭 k (y i)) = x := by
  choose f hf using fun z : 𝓞 K ⧸ extP K 𝔭 ^ k => Ideal.Quotient.mk_surjective z
  exact ⟨fun i => f (x i), funext fun i => hf _⟩

/- English proof (translation)
Take `⟨y, rfl⟩` from `exists_liftv 𝔭 (k + 1) x`. Rewrite using `[Qc_mk (by omega) H y]`. Conclude with `Qc_mk hck H y`.
-/
theorem Qc_piQ {𝔭 : Ideal (𝓞 F)} {k c : ℕ} (hck : c + 1 ≤ k) (H : Matrix m m (𝓞 K))
    (x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :
    Qc 𝔭 k c H (fun i => piQ K 𝔭 k (x i)) ↔ Qc 𝔭 (k + 1) c H x := by
  obtain ⟨y, rfl⟩ := exists_liftv 𝔭 (k + 1) x
  rw [Qc_mk (by omega) H y]
  exact Qc_mk hck H y

/- English proof (translation)
Establish `hs : star (fun i => mkk K 𝔭 k (x i)) = fun i => mkk K 𝔭 k (star x i)`. Use function extensionality and compare the values at `i`. Conclude with `idealPowerSpanBounds.star_mk 𝔭 k (x i)`. Establish `hv : H.map (mkk K 𝔭 k) *ᵥ (fun i => mkk K 𝔭 k (y i)) = fun i => mkk K 𝔭 k ((H *ᵥ y) i)`. Use function extensionality and compare the values at `i`.

Conclude with `(RingHom.map_mulVec (mkk K 𝔭 k) H y i).symm`. Use `show star (fun i => mkk K 𝔭 k (x i)) ⬝ᵥ (H.map (mkk K 𝔭 k) *ᵥ (fun i => mkk K 𝔭 k (y i))) = mkk K 𝔭 k (star x ⬝ᵥ (H *ᵥ y))`. Rewrite using `[hs, hv, RingHom.map_dotProduct]`. Both sides reduce to the same expression.
-/
theorem mk_fm (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix m m (𝓞 K)) (x y : m → 𝓞 K) :
    fm (H.map (mkk K 𝔭 k)) (fun i => mkk K 𝔭 k (x i)) (fun i => mkk K 𝔭 k (y i)) =
      mkk K 𝔭 k (fm H x y) := by
  have hs : star (fun i => mkk K 𝔭 k (x i)) = fun i => mkk K 𝔭 k (star x i) := by
    funext i
    exact idealPowerSpanBounds.star_mk 𝔭 k (x i)
  have hv : H.map (mkk K 𝔭 k) *ᵥ (fun i => mkk K 𝔭 k (y i)) =
      fun i => mkk K 𝔭 k ((H *ᵥ y) i) := by
    funext i
    exact (RingHom.map_mulVec (mkk K 𝔭 k) H y i).symm
  show star (fun i => mkk K 𝔭 k (x i)) ⬝ᵥ (H.map (mkk K 𝔭 k) *ᵥ (fun i => mkk K 𝔭 k (y i))) =
    mkk K 𝔭 k (star x ⬝ᵥ (H *ᵥ y))
  rw [hs, hv, RingHom.map_dotProduct]
  rfl

def nkQ (𝔭 : Ideal (𝓞 F)) (k c : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) : ℕ :=
  Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // Qc 𝔭 k c H x ∧
    fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)}

def nkM (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) : ℕ :=
  Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)}

/- English proof (translation)
Establish `hF : IsFixF K F` using `Fact.out`. Establish `hck : c + 1 ≤ k` using `by omega`. Establish `hj : k + 1 ≤ 2 * (k - c)` using `by omega`. Establish `hinv : ∀ x y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ (k - c)) → (Qc 𝔭 k c H (fun i => mkk K 𝔭 k ((x + y) i)) ↔ Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i)))`. Introduce `x y hy`.

Rewrite using `[Qc_mk hck H, Qc_mk hck H]`. Establish `hy' : ∀ j', (star y ᵥ* H) j' ∈ extP K 𝔭 ^ (c + 1)` using `fun j' => Ideal.pow_le_pow_right (by omega) (vecMul_mem (fun a => conjO_mem_pow hF 𝔭 (k - c) _ (hy a)) H j')`. Establish `e : ∀ j', (star (x + y) ᵥ* H) j' = (star x ᵥ* H) j' + (star y ᵥ* H) j'`. Introduce `j'`. Rewrite using `[star_add, Matrix.add_vecMul]`.

Both sides reduce to the same expression. Simplify using `only [e]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j', hj'⟩`. Conclude with `⟨j', fun h => hj' (Ideal.add_mem _ h (hy' j'))⟩`.

Introduce and unpack `⟨j', hj'⟩`. Use `⟨j', fun h => hj' ?_⟩` and prove the remaining obligations. Establish `h2` using `Ideal.sub_mem _ h (hy' j')`. Simplify using `using h2`. Establish `RC : ∀ x : m → 𝓞 K, Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i)) → fm H x x - ι n ∈ extP K 𝔭 ^ k → ∀ s ∈ extP K 𝔭 ^ k, star s - s ∈ extP K 𝔭 ^ (k + 1) → ∃ y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ (k - c)) ∧ fm H x y + fm H y x - s ∈ extP K 𝔭 ^ (k + 1)`.

Introduce `x hQ _ s hs hs'`. Take `⟨j0, hj0⟩` from `(Qc_mk hck H x).mp hQ`. Take `⟨r, hr, hr'⟩` from `exists_solve_scalar hK hF h𝔭 (by omega : c ≤ k) hj0 hs hs'`. Use `⟨Pi.single j0 r, fun a => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `ha : a = j0`.

Substitute `ha` using the available equality. Simplify using `using hr`. Simplify using `[Pi.single_apply, ha]`. Establish `e1 : fm H x (Pi.single j0 r) = (star x ᵥ* H) j0 * r`. Rewrite using `[fm_eq]`.

Use `first`. Consider the case `exact dotProduct_single _ _ _`. Consider the case `simp [dotProduct, Pi.single_apply]`. Rewrite using `[fm_star hH x (Pi.single j0 r), e1]`. Conclude with `hr'`.

Establish `h` using `card_vec_succ hK h𝔭 H hH n hj (Qc 𝔭 k c H) hinv RC`. Establish `e : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // Qc 𝔭 k c H (fun i => piQ K 𝔭 k (x i)) ∧ fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} = nkQ 𝔭 (k + 1) c H n` using `Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [Qc_piQ hck H x]))`. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem nkQ_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) (n : 𝓞 F) {c k : ℕ} (hk : 2 * c + 1 ≤ k) :
    nkQ 𝔭 (k + 1) c H n * Ideal.absNorm 𝔭 = Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkQ 𝔭 k c H n := by
  have hF : IsFixF K F := Fact.out
  have hck : c + 1 ≤ k := by omega
  have hj : k + 1 ≤ 2 * (k - c) := by omega
  have hinv : ∀ x y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ (k - c)) →
      (Qc 𝔭 k c H (fun i => mkk K 𝔭 k ((x + y) i)) ↔ Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i))) := by
    intro x y hy
    rw [Qc_mk hck H, Qc_mk hck H]
    have hy' : ∀ j', (star y ᵥ* H) j' ∈ extP K 𝔭 ^ (c + 1) := fun j' =>
      Ideal.pow_le_pow_right (by omega)
        (vecMul_mem (fun a => conjO_mem_pow hF 𝔭 (k - c) _ (hy a)) H j')
    have e : ∀ j', (star (x + y) ᵥ* H) j' = (star x ᵥ* H) j' + (star y ᵥ* H) j' := by
      intro j'
      rw [star_add, Matrix.add_vecMul]
      rfl
    simp only [e]
    constructor
    · rintro ⟨j', hj'⟩
      exact ⟨j', fun h => hj' (Ideal.add_mem _ h (hy' j'))⟩
    · rintro ⟨j', hj'⟩
      refine ⟨j', fun h => hj' ?_⟩
      have h2 := Ideal.sub_mem _ h (hy' j')
      simpa using h2
  have RC : ∀ x : m → 𝓞 K, Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i)) →
      fm H x x - ι n ∈ extP K 𝔭 ^ k → ∀ s ∈ extP K 𝔭 ^ k, star s - s ∈ extP K 𝔭 ^ (k + 1) →
      ∃ y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ (k - c)) ∧
        fm H x y + fm H y x - s ∈ extP K 𝔭 ^ (k + 1) := by
    intro x hQ _ s hs hs'
    obtain ⟨j0, hj0⟩ := (Qc_mk hck H x).mp hQ
    obtain ⟨r, hr, hr'⟩ := exists_solve_scalar hK hF h𝔭 (by omega : c ≤ k) hj0 hs hs'
    refine ⟨Pi.single j0 r, fun a => ?_, ?_⟩
    · by_cases ha : a = j0
      · subst ha
        simpa using hr
      · simp [Pi.single_apply, ha]
    · have e1 : fm H x (Pi.single j0 r) = (star x ᵥ* H) j0 * r := by
        rw [fm_eq]
        first
        | exact dotProduct_single _ _ _
        | simp [dotProduct, Pi.single_apply]
      rw [fm_star hH x (Pi.single j0 r), e1]
      exact hr'
  have h := card_vec_succ hK h𝔭 H hH n hj (Qc 𝔭 k c H) hinv RC
  have e : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) //
      Qc 𝔭 k c H (fun i => piQ K 𝔭 k (x i)) ∧
        fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} = nkQ 𝔭 (k + 1) c H n :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [Qc_piQ hck H x]))
  rw [e] at h
  exact h

/- English proof (translation)
Establish `hF : IsFixF K F` using `Fact.out`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `h1 : ∀ i, ι D * star (x i) ∈ extP K 𝔭 ^ (c + 1)`. Introduce `i`.

Establish `h2` using `vecMul_mem hall H.adjugate i`. Rewrite `h2` using `[vecMul_adjugate, hD, Pi.smul_apply, smul_eq_mul]`. Conclude with `h2`. Establish `h3 : ∀ i, ι D * x i ∈ extP K 𝔭 ^ (c + 1)`. Introduce `i`.

Establish `h4` using `conjO_mem_pow hF 𝔭 (c + 1) _ (h1 i)`. Rewrite `h4` using `[map_mul, conjO_map hF, ← idealPowerSpanBounds.star_def, star_star]`. Conclude with `h4`. Establish `h5 : ι D * fm H x x ∈ extP K 𝔭 ^ (d + v + 1)`. Rewrite using `[fm_eq]`.

Simplify using `only [dotProduct, Finset.mul_sum]`. Use `Ideal.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Establish `h6 : (star x ᵥ* H) i * (ι D * x i) ∈ extP K 𝔭 ^ ((c + 1) + (c + 1))`. Rewrite using `[pow_add]`. Conclude with `Ideal.mul_mem_mul (hall i) (h3 i)`.

Establish `e : ι D * ((star x ᵥ* H) i * x i) = (star x ᵥ* H) i * (ι D * x i)` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.pow_le_pow_right (by omega) h6`. Establish `h7 : ι D * (fm H x x - ι n) ∈ extP K 𝔭 ^ (d + v + 1)` using `Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk hx)`. Establish `h8 : ι (D * n) ∈ extP K 𝔭 ^ (d + v + 1)`.

Establish `e : ι (D * n) = ι D * fm H x x - ι D * (fm H x x - ι n)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ h5 h7`.

Rewrite `h8` using `[mem_pow_iff]`. Conclude with `idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hDd hn h8`.
-/
theorem exists_notMem_of_sol {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {H : Matrix m m (𝓞 K)}
    (hH : Hᴴ = H) {D n : 𝓞 F} (hD : H.det = ι D) {d v c k : ℕ} (hDd : D ∉ 𝔭 ^ (d + 1))
    (hn : n ∉ 𝔭 ^ (v + 1)) (hk : d + v + 1 ≤ k) (hc : d + v + 1 ≤ 2 * (c + 1)) {x : m → 𝓞 K}
    (hx : fm H x x - ι n ∈ extP K 𝔭 ^ k) : ∃ j, (star x ᵥ* H) j ∉ extP K 𝔭 ^ (c + 1) := by
  have hF : IsFixF K F := Fact.out
  by_contra hall
  push_neg at hall
  have h1 : ∀ i, ι D * star (x i) ∈ extP K 𝔭 ^ (c + 1) := by
    intro i
    have h2 := vecMul_mem hall H.adjugate i
    rw [vecMul_adjugate, hD, Pi.smul_apply, smul_eq_mul] at h2
    exact h2
  have h3 : ∀ i, ι D * x i ∈ extP K 𝔭 ^ (c + 1) := by
    intro i
    have h4 := conjO_mem_pow hF 𝔭 (c + 1) _ (h1 i)
    rw [map_mul, conjO_map hF, ← idealPowerSpanBounds.star_def, star_star] at h4
    exact h4
  have h5 : ι D * fm H x x ∈ extP K 𝔭 ^ (d + v + 1) := by
    rw [fm_eq]
    simp only [dotProduct, Finset.mul_sum]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    have h6 : (star x ᵥ* H) i * (ι D * x i) ∈ extP K 𝔭 ^ ((c + 1) + (c + 1)) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul (hall i) (h3 i)
    have e : ι D * ((star x ᵥ* H) i * x i) = (star x ᵥ* H) i * (ι D * x i) := by ring
    rw [e]
    exact Ideal.pow_le_pow_right (by omega) h6
  have h7 : ι D * (fm H x x - ι n) ∈ extP K 𝔭 ^ (d + v + 1) :=
    Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk hx)
  have h8 : ι (D * n) ∈ extP K 𝔭 ^ (d + v + 1) := by
    have e : ι (D * n) = ι D * fm H x x - ι D * (fm H x x - ι n) := by
      rw [map_mul]
      ring
    rw [e]
    exact Ideal.sub_mem _ h5 h7
  rw [mem_pow_iff] at h8
  exact idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hDd hn h8

/- English proof (translation)
Unfold `nkM nkQ`. Use `Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨?_, hx⟩` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `exists_liftv 𝔭 k x`. Rewrite using `[Qc_mk hck H y]`. Rewrite `hx` using `[mk_fm]`. Establish `hy : fm H y y - ι n ∈ extP K 𝔭 ^ k` using `Ideal.Quotient.eq.mp hx`. Conclude with `exists_notMem_of_sol h𝔭 hH hD hDd hn hk hc hy`.

Conclude with `fun h => h.2`.
-/
theorem nkM_eq_nkQ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {H : Matrix m m (𝓞 K)}
    (hH : Hᴴ = H) {D n : 𝓞 F} (hD : H.det = ι D) {d v c k : ℕ} (hDd : D ∉ 𝔭 ^ (d + 1))
    (hn : n ∉ 𝔭 ^ (v + 1)) (hk : d + v + 1 ≤ k) (hc : d + v + 1 ≤ 2 * (c + 1)) (hck : c + 1 ≤ k) :
    nkM 𝔭 k H n = nkQ 𝔭 k c H n := by
  unfold nkM nkQ
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
  constructor
  · intro hx
    refine ⟨?_, hx⟩
    obtain ⟨y, rfl⟩ := exists_liftv 𝔭 k x
    rw [Qc_mk hck H y]
    rw [mk_fm] at hx
    have hy : fm H y y - ι n ∈ extP K 𝔭 ^ k := Ideal.Quotient.eq.mp hx
    exact exists_notMem_of_sol h𝔭 hH hD hDd hn hk hc hy
  · exact fun h => h.2

/- English proof (translation)
Take `⟨c, hcdef⟩ : ∃ c, c = (d + v) / 2` from `⟨_, rfl⟩`. Establish `hc : d + v + 1 ≤ 2 * (c + 1)` using `by omega`. Establish `h2c : 2 * c + 1 ≤ k` using `by omega`. Rewrite using `[nkM_eq_nkQ (k := k + 1) (c := c) h𝔭 hH hD hDd hn (by omega) hc (by omega), nkM_eq_nkQ (k := k) (c := c) h𝔭 hH hD hDd hn hk hc (by omega)]`. Conclude with `nkQ_succ hK h𝔭 hH n h2c`.
-/
theorem nkM_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D n : 𝓞 F} (hD : H.det = ι D) {d v k : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (hn : n ∉ 𝔭 ^ (v + 1)) (hk : d + v + 1 ≤ k) :
    nkM 𝔭 (k + 1) H n * Ideal.absNorm 𝔭 = Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkM 𝔭 k H n := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = (d + v) / 2 := ⟨_, rfl⟩
  have hc : d + v + 1 ≤ 2 * (c + 1) := by omega
  have h2c : 2 * c + 1 ≤ k := by omega
  rw [nkM_eq_nkQ (k := k + 1) (c := c) h𝔭 hH hD hDd hn (by omega) hc (by omega),
    nkM_eq_nkQ (k := k) (c := c) h𝔭 hH hD hDd hn hk hc (by omega)]
  exact nkQ_succ hK h𝔭 hH n h2c

end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
