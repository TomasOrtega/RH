import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryStabiliserOrthogonalSummand
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

section FrameAction

variable {R R' : Type} [CommRing R] [CommRing R']
  {N ι κ : Type} [Fintype N] [DecidableEq N] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def frameAct (Q : Matrix N (ι ⊕ κ) R) (Qi : Matrix (ι ⊕ κ) N R) (y : Matrix ι ι R) : Matrix N N R :=
  Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi

variable {Q : Matrix N (ι ⊕ κ) R} {Qi : Matrix (ι ⊕ κ) N R}

/- English proof (translation)
Simplify using `only [frameAct, Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
theorem frameAct_mul_frame (h2 : Qi * Q = 1) (y : Matrix ι ι R) :
    frameAct Q Qi y * Q = Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) := by
  simp only [frameAct, Matrix.mul_assoc, h2, Matrix.mul_one]

/- English proof (translation)
Simplify using `only [frameAct, Matrix.fromBlocks_one, Matrix.mul_one, h1]`.
-/
theorem frameAct_one (h1 : Q * Qi = 1) : frameAct Q Qi (1 : Matrix ι ι R) = 1 := by
  simp only [frameAct, Matrix.fromBlocks_one, Matrix.mul_one, h1]

/- English proof (translation)
Establish `hB : Matrix.fromBlocks (y * y') 0 0 (1 : Matrix κ κ R) = Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Matrix.fromBlocks y' 0 0 (1 : Matrix κ κ R)`. Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules. Simplify using `only [frameAct, hB, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Qi Q, h2, Matrix.one_mul]`.
-/
theorem frameAct_mul (h2 : Qi * Q = 1) (y y' : Matrix ι ι R) :
    frameAct Q Qi (y * y') = frameAct Q Qi y * frameAct Q Qi y' := by
  have hB : Matrix.fromBlocks (y * y') 0 0 (1 : Matrix κ κ R) =
      Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Matrix.fromBlocks y' 0 0 (1 : Matrix κ κ R) := by
    rw [Matrix.fromBlocks_multiply]; simp
  simp only [frameAct, hB, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Qi Q, h2, Matrix.one_mul]

/- English proof (translation)
Use extensionality with `i j`. Establish `key : ∀ z : Matrix ι ι R, (Qi * (Q * Matrix.fromBlocks z 0 0 (1 : Matrix κ κ R))) (Sum.inl i) (Sum.inl j) = z i j`. Introduce `z`. Rewrite using `[← Matrix.mul_assoc, h2, Matrix.one_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[← key y, ← key y', Matrix.mul_apply (M := Qi), Matrix.mul_apply (M := Qi)]`. Conclude with `Finset.sum_congr rfl fun l _ => by rw [hc l j]`.
-/
theorem frame_block_inj (h2 : Qi * Q = 1) {y y' : Matrix ι ι R}
    (hc : ∀ l j, (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) l (Sum.inl j) =
      (Q * Matrix.fromBlocks y' 0 0 (1 : Matrix κ κ R)) l (Sum.inl j)) : y = y' := by
  ext i j
  have key : ∀ z : Matrix ι ι R,
      (Qi * (Q * Matrix.fromBlocks z 0 0 (1 : Matrix κ κ R))) (Sum.inl i) (Sum.inl j) = z i j := by
    intro z
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
    simp
  rw [← key y, ← key y', Matrix.mul_apply (M := Qi), Matrix.mul_apply (M := Qi)]
  exact Finset.sum_congr rfl fun l _ => by rw [hc l j]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h` using `congrFun (congrFun (frameAct_mul_frame h2 y) i) (Sum.inr b)`. Use `show ∑ x, frameAct Q Qi y i x * Q x (Sum.inr b) = Q i (Sum.inr b)`. Rewrite using `[← Matrix.mul_apply, h]`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`.
-/
theorem frameAct_col_inr (h2 : Qi * Q = 1) (y : Matrix ι ι R) (b : κ) :
    frameAct Q Qi y *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b) := by
  funext i
  have h := congrFun (congrFun (frameAct_mul_frame h2 y) i) (Sum.inr b)
  show ∑ x, frameAct Q Qi y i x * Q x (Sum.inr b) = Q i (Sum.inr b)
  rw [← Matrix.mul_apply, h]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/- English proof (translation)
Establish `e1 : ∀ j l, (M *ᵥ fun l => Q l (Sum.inl j)) l = (M * Q) l (Sum.inl j)` using `fun _ _ => rfl`. Establish `e2 : ∀ j l, (∑ i, y i j • fun l => Q l (Sum.inl i)) l = (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) l (Sum.inl j)`. Introduce `j l`. Simplify using `[Finset.sum_apply, Matrix.mul_apply, Fintype.sum_sum_type, mul_comm]`. Prove the components needed by the constructor for the conclusion.

Introduce `h l j`. Rewrite using `[← e1, ← e2, h j]`. Introduce `h j`. Use function extensionality and compare the values at `l`. Rewrite using `[e1, e2, h l j]`.
-/
theorem frame_rep_iff (M : Matrix N N R) (y : Matrix ι ι R) :
    (∀ j, M *ᵥ (fun l => Q l (Sum.inl j)) = ∑ i, y i j • (fun l => Q l (Sum.inl i))) ↔
      ∀ l j, (M * Q) l (Sum.inl j) = (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) l (Sum.inl j) := by
  have e1 : ∀ j l, (M *ᵥ fun l => Q l (Sum.inl j)) l = (M * Q) l (Sum.inl j) := fun _ _ => rfl
  have e2 : ∀ j l, (∑ i, y i j • fun l => Q l (Sum.inl i)) l =
      (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) l (Sum.inl j) := by
    intro j l
    simp [Finset.sum_apply, Matrix.mul_apply, Fintype.sum_sum_type, mul_comm]
  constructor
  · intro h l j
    rw [← e1, ← e2, h j]
  · intro h j
    funext l
    rw [e1, e2, h l j]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.
-/
theorem map_mul_equiv {l m n : Type} [Fintype m] (e : R ≃+* R') (A : Matrix l m R) (B : Matrix m n R) :
    (A * B).map e = A.map e * B.map e := by
  ext i j
  simp [Matrix.mul_apply]

/- English proof (translation)
Establish `h1 : (y.map e).map s' = (y.map s).map e`. Use extensionality with `i j`. Simplify using `[he]`. Rewrite using `[h1, ← Matrix.transpose_map, ← map_mul_equiv, ← map_mul_equiv, hy]`.
-/
theorem unitary_map_equiv (s : R →+* R) (s' : R' →+* R') (e : R ≃+* R') (he : ∀ a, e (s a) = s' (e a))
    (G y : Matrix ι ι R) (hy : (y.map s)ᵀ * G * y = G) :
    ((y.map e).map s')ᵀ * G.map e * y.map e = G.map e := by
  have h1 : (y.map e).map s' = (y.map s).map e := by
    ext i j; simp [he]
  rw [h1, ← Matrix.transpose_map, ← map_mul_equiv, ← map_mul_equiv, hy]

/- English proof (translation)
Take `⟨hfwd, hbwd⟩` from `unitary_stabiliser_orthogonal_summand R s N ι κ J G G' Q Qi h1 h2 hD hG'`. Set `yOf : Matrix N N R → Matrix ι ι R` to `fun M => (Qi * M * Q).toBlocks₁₁`. Establish `yOf_frame : ∀ y, yOf (frameAct Q Qi y) = y`. Introduce `y`. Use `show (Qi * (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi) * Q).toBlocks₁₁ = y`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Qi Q, h2, Matrix.one_mul, Matrix.mul_one]`. Conclude with `Matrix.toBlocks_fromBlocks₁₁ _ _ _ _`. Establish `memH : ∀ x : U, x ∈ H → ((yOf x.1.1).map s)ᵀ * G * yOf x.1.1 = G ∧ x.1.1 = frameAct Q Qi (yOf x.1.1)`. Introduce `x hx`.

Take `⟨y, hy, hxy⟩` from `hbwd x.1.1 ((hU x.1).1 x.2) ((hH x).1 hx)`. Establish `hyx : yOf x.1.1 = y` using `by rw [hxy]; exact yOf_frame y`. Rewrite using `[hyx]`. Conclude with `⟨hy, hxy⟩`. Set `φ0 : H →* Matrix ι ι R` to `{ toFun := fun h => yOf h.1.1.1 map_one' := by`.

Establish `h1'` using `yOf_frame 1`. Rewrite `h1'` using `[frameAct_one h1]`. Conclude with `h1'`. Use the proof step `map_mul' := by`. Introduce `a b`.

Take `⟨-, ha⟩` from `memH a.1 a.2`. Take `⟨-, hb⟩` from `memH b.1 b.2`. Use `show yOf (a.1.1.1 * b.1.1.1) = yOf a.1.1.1 * yOf b.1.1.1`. Use `conv_lhs => rw [ha, hb, ← frameAct_mul h2, yOf_frame] }`. Set `φ1 : H →* GL ι R'` to `(Units.map (e.mapMatrix (m := ι)).toMonoidHom).comp φ0.toHomUnits`.

Establish `φ1_val : ∀ h : H, ((φ1 h : GL ι R') : Matrix ι ι R') = (yOf h.1.1.1).map e` using `fun _ => rfl`. Establish `memU' : ∀ h : H, φ1 h ∈ U'`. Introduce `h`. Rewrite using `[hU', φ1_val]`. Conclude with `unitary_map_equiv s s' e he G _ (memH h.1 h.2).1`.

Set `Φ0 : H →* U'` to `φ1.codRestrict U' memU'`. Establish `hinj : Function.Injective Φ0`. Introduce `a b hab`. Establish `e1 : (yOf a.1.1.1).map e = (yOf b.1.1.1).map e`. Rewrite using `[← φ1_val, ← φ1_val]`.

Conclude with `congrArg (fun z : U' => ((z : GL ι R') : Matrix ι ι R')) hab`. Establish `e2 : yOf a.1.1.1 = yOf b.1.1.1`. Use extensionality with `i j`. Conclude with `e.injective (congrFun (congrFun e1 i) j)`. Establish `e3 : a.1.1.1 = b.1.1.1`.

Rewrite using `[(memH a.1 a.2).2, (memH b.1 b.2).2, e2]`. Conclude with `Subtype.ext (Subtype.ext (Units.ext e3))`. Establish `hsurj : Function.Surjective Φ0`. Introduce `y`. Establish `he' : ∀ a, e.symm (s' a) = s (e.symm a)`.

Introduce `a`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply]`. Establish `hGG : (G.map e).map e.symm = G`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Establish `hzu : ((((y : GL ι R') : Matrix ι ι R').map e.symm).map s)ᵀ * G * ((y : GL ι R') : Matrix ι ι R').map e.symm = G`. Establish `h3` using `unitary_map_equiv s' s e.symm he' (G.map e) _ ((hU' y.1).1 y.2)`. Rewrite `h3` using `[hGG]`. Then use the resulting hypothesis. Establish `hinv : ∀ a b : U', a * b = 1 → ((a : GL ι R') : Matrix ι ι R').map e.symm * ((b : GL ι R') : Matrix ι ι R').map e.symm = 1`.

Introduce `a b hab`. Rewrite using `[← map_mul_equiv]`. Establish `hab' : ((a : GL ι R') : Matrix ι ι R') * ((b : GL ι R') : Matrix ι ι R') = 1`. Use `congrArg (fun z : U' => ((z : GL ι R') : Matrix ι ι R')) hab` as an intermediate fact. Conclude with `this`.

Rewrite using `[hab']`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Set `g : GL N R` to `⟨frameAct Q Qi (((y : GL ι R') : Matrix ι ι R').map e.symm), frameAct Q Qi ((((y⁻¹ : U') : GL ι R') : Matrix ι ι R').map e.symm), by rw [← frameAct_mul h2, hinv y y⁻¹ (mul_inv_cancel y), frameAct_one h1], by rw [← frameAct_mul h2, hinv y⁻¹ y (inv_mul_cancel y), frameAct_one h1]⟩`. Establish `gU : g ∈ U` using `(hU g).2 (hfwd _ hzu)`.

Establish `gH : (⟨g, gU⟩ : U) ∈ H` using `(hH _).2 (fun b => frameAct_col_inr h2 _ b)`. Use `⟨⟨⟨g, gU⟩, gH⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show (yOf (frameAct Q Qi (((y : GL ι R') : Matrix ι ι R').map e.symm))).map e = ((y : GL ι R') : Matrix ι ι R')`.

Rewrite using `[yOf_frame]`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Set `Φ : H ≃* U'` to `MulEquiv.ofBijective Φ0 ⟨hinj, hsurj⟩`. Use `⟨Φ, fun h y => ?_⟩` and prove the remaining obligations.

Establish `hΦ : (((Φ h : U') : GL ι R') : Matrix ι ι R') = (yOf h.1.1.1).map e` using `rfl`. Take `⟨-, hh⟩` from `memH h.1 h.2`. Establish `hm : h.1.1.1 * Q = Q * Matrix.fromBlocks (yOf h.1.1.1) 0 0 (1 : Matrix κ κ R)` using `by conv_lhs => rw [hh]`. Conclude with `frameAct_mul_frame h2 _`. Use `show (∀ j, h.1.1.1 *ᵥ (fun l => Q l (Sum.inl j)) = ∑ i, (((y : GL ι R') : Matrix ι ι R').map e.symm) i j • (fun l => Q l (Sum.inl i))) ↔ Φ h = y`.

Rewrite using `[frame_rep_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hc`. Establish `hy : yOf h.1.1.1 = ((y : GL ι R') : Matrix ι ι R').map e.symm`. Apply `frame_block_inj h2` to reduce the goal to its premises.

Introduce `l j`. Rewrite using `[← hm]`. Conclude with `hc l j`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[hΦ, hy]`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Introduce `hΦy l j`. Establish `hy : yOf h.1.1.1 = ((y : GL ι R') : Matrix ι ι R').map e.symm`.

Rewrite using `[← hΦy, hΦ]`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hm, hy]`.
-/
theorem frame_stabiliser_mulEquiv (s : R →+* R) (s' : R' →+* R') (e : R ≃+* R')
    (he : ∀ a, e (s a) = s' (e a)) (J : Matrix N N R) (G : Matrix ι ι R) (G' : Matrix κ κ R)
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (hD : (Q.map s)ᵀ * J * Q = Matrix.fromBlocks G 0 0 G') (hG' : IsUnit G'.det)
    (U : Subgroup (GL N R)) (hU : ∀ g : GL N R, g ∈ U ↔ (g.1.map s)ᵀ * J * g.1 = J)
    (U' : Subgroup (GL ι R'))
    (hU' : ∀ g : GL ι R', g ∈ U' ↔ (g.1.map s')ᵀ * G.map e * g.1 = G.map e)
    (H : Subgroup U)
    (hH : ∀ x : U, x ∈ H ↔ ∀ b, x.1.1 *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b)) :
    ∃ Φ : H ≃* U', ∀ (h : H) (y : U'),
      (∀ j, h.1.1.1 *ᵥ (fun l => Q l (Sum.inl j)) =
        ∑ i, e.symm (y.1.1 i j) • (fun l => Q l (Sum.inl i))) ↔ Φ h = y := by
  classical
  obtain ⟨hfwd, hbwd⟩ := unitary_stabiliser_orthogonal_summand R s N ι κ J G G' Q Qi h1 h2 hD hG'

  let yOf : Matrix N N R → Matrix ι ι R := fun M => (Qi * M * Q).toBlocks₁₁
  have yOf_frame : ∀ y, yOf (frameAct Q Qi y) = y := by
    intro y
    show (Qi * (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi) * Q).toBlocks₁₁ = y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qi Q, h2, Matrix.one_mul, Matrix.mul_one]
    exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

  have memH : ∀ x : U, x ∈ H →
      ((yOf x.1.1).map s)ᵀ * G * yOf x.1.1 = G ∧ x.1.1 = frameAct Q Qi (yOf x.1.1) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hbwd x.1.1 ((hU x.1).1 x.2) ((hH x).1 hx)
    have hyx : yOf x.1.1 = y := by rw [hxy]; exact yOf_frame y
    rw [hyx]
    exact ⟨hy, hxy⟩

  let φ0 : H →* Matrix ι ι R :=
    { toFun := fun h => yOf h.1.1.1
      map_one' := by
        have h1' := yOf_frame 1
        rw [frameAct_one h1] at h1'
        exact h1'
      map_mul' := by
        intro a b
        obtain ⟨-, ha⟩ := memH a.1 a.2
        obtain ⟨-, hb⟩ := memH b.1 b.2
        show yOf (a.1.1.1 * b.1.1.1) = yOf a.1.1.1 * yOf b.1.1.1
        conv_lhs => rw [ha, hb, ← frameAct_mul h2, yOf_frame] }
  let φ1 : H →* GL ι R' :=
    (Units.map (e.mapMatrix (m := ι)).toMonoidHom).comp φ0.toHomUnits
  have φ1_val : ∀ h : H, ((φ1 h : GL ι R') : Matrix ι ι R') = (yOf h.1.1.1).map e := fun _ => rfl
  have memU' : ∀ h : H, φ1 h ∈ U' := by
    intro h
    rw [hU', φ1_val]
    exact unitary_map_equiv s s' e he G _ (memH h.1 h.2).1
  let Φ0 : H →* U' := φ1.codRestrict U' memU'
  have hinj : Function.Injective Φ0 := by
    intro a b hab
    have e1 : (yOf a.1.1.1).map e = (yOf b.1.1.1).map e := by
      rw [← φ1_val, ← φ1_val]
      exact congrArg (fun z : U' => ((z : GL ι R') : Matrix ι ι R')) hab
    have e2 : yOf a.1.1.1 = yOf b.1.1.1 := by
      ext i j
      exact e.injective (congrFun (congrFun e1 i) j)
    have e3 : a.1.1.1 = b.1.1.1 := by
      rw [(memH a.1 a.2).2, (memH b.1 b.2).2, e2]
    exact Subtype.ext (Subtype.ext (Units.ext e3))
  have hsurj : Function.Surjective Φ0 := by
    intro y
    have he' : ∀ a, e.symm (s' a) = s (e.symm a) := by
      intro a
      apply e.injective
      rw [RingEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply]
    have hGG : (G.map e).map e.symm = G := by
      ext i j; simp
    have hzu : ((((y : GL ι R') : Matrix ι ι R').map e.symm).map s)ᵀ * G *
        ((y : GL ι R') : Matrix ι ι R').map e.symm = G := by
      have h3 := unitary_map_equiv s' s e.symm he' (G.map e) _ ((hU' y.1).1 y.2)
      rwa [hGG] at h3
    have hinv : ∀ a b : U', a * b = 1 →
        ((a : GL ι R') : Matrix ι ι R').map e.symm * ((b : GL ι R') : Matrix ι ι R').map e.symm = 1 := by
      intro a b hab
      rw [← map_mul_equiv]
      have hab' : ((a : GL ι R') : Matrix ι ι R') * ((b : GL ι R') : Matrix ι ι R') = 1 := by
        have := congrArg (fun z : U' => ((z : GL ι R') : Matrix ι ι R')) hab
        exact this
      rw [hab']
      ext i j
      simp [Matrix.one_apply]
    let g : GL N R :=
      ⟨frameAct Q Qi (((y : GL ι R') : Matrix ι ι R').map e.symm),
        frameAct Q Qi ((((y⁻¹ : U') : GL ι R') : Matrix ι ι R').map e.symm),
        by rw [← frameAct_mul h2, hinv y y⁻¹ (mul_inv_cancel y), frameAct_one h1],
        by rw [← frameAct_mul h2, hinv y⁻¹ y (inv_mul_cancel y), frameAct_one h1]⟩
    have gU : g ∈ U := (hU g).2 (hfwd _ hzu)
    have gH : (⟨g, gU⟩ : U) ∈ H := (hH _).2 (fun b => frameAct_col_inr h2 _ b)
    refine ⟨⟨⟨g, gU⟩, gH⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    show (yOf (frameAct Q Qi (((y : GL ι R') : Matrix ι ι R').map e.symm))).map e = ((y : GL ι R') : Matrix ι ι R')
    rw [yOf_frame]
    ext i j
    simp
  let Φ : H ≃* U' := MulEquiv.ofBijective Φ0 ⟨hinj, hsurj⟩
  refine ⟨Φ, fun h y => ?_⟩
  have hΦ : (((Φ h : U') : GL ι R') : Matrix ι ι R') = (yOf h.1.1.1).map e := rfl
  obtain ⟨-, hh⟩ := memH h.1 h.2
  have hm : h.1.1.1 * Q = Q * Matrix.fromBlocks (yOf h.1.1.1) 0 0 (1 : Matrix κ κ R) := by
    conv_lhs => rw [hh]
    exact frameAct_mul_frame h2 _
  show (∀ j, h.1.1.1 *ᵥ (fun l => Q l (Sum.inl j)) =
      ∑ i, (((y : GL ι R') : Matrix ι ι R').map e.symm) i j • (fun l => Q l (Sum.inl i))) ↔ Φ h = y
  rw [frame_rep_iff]
  constructor
  · intro hc
    have hy : yOf h.1.1.1 = ((y : GL ι R') : Matrix ι ι R').map e.symm := by
      apply frame_block_inj h2
      intro l j
      rw [← hm]
      exact hc l j
    apply Subtype.ext
    apply Units.ext
    rw [hΦ, hy]
    ext i j
    simp
  · intro hΦy l j
    have hy : yOf h.1.1.1 = ((y : GL ι R') : Matrix ι ι R').map e.symm := by
      rw [← hΦy, hΦ]
      ext i j
      simp
    rw [hm, hy]

end FrameAction

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `D X u wt ιA hW hA hσ`. Take `⟨Q, Qi, G', h1, h2, hQl, hQe, hQf, hQz, hG', hD⟩` from `GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW`. Use `set f : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) with hf`. Establish `hA1 : Q.map f * Qi.map f = 1`. Rewrite using `[← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)]`.

Establish `hA2 : Qi.map f * Q.map f = 1`. Rewrite using `[← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)]`. Establish `hsf : ∀ x, sigA X.B.I (f x) = f (star x)`. Introduce `x`. Simplify using `only [hf, sigA, Formalism.UG.sigR, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`.

Both sides reduce to the same expression. Establish `hDA : ((Q.map f).map (sigA X.B.I))ᵀ * X.B.I.J.map f * Q.map f = Matrix.fromBlocks (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).map f) 0 0 (G'.map f)`. Establish `hs : (Q.map f).map (sigA X.B.I) = (Q.map (starRingEnd X.B.I.E)).map f`. Use extensionality with `i j`. Conclude with `hsf (Q i j)`.

Rewrite using `[hs, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hD, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f), Matrix.map_zero _ (map_zero f)]`. Establish `hGA : IsUnit (G'.map f).det`. Establish `h3` using `hG'.map f`. Rewrite `h3` using `[RingHom.map_det]`. Then use the resulting hypothesis. Establish `hGm : (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).map f).map ιA = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map (Formalism.UG.inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`. Rewrite using `[hf, hA.1, RingEquiv.apply_symm_apply]`. Establish `hH : ∀ x : X.B.I.Gf, x ∈ Hfin X u ↔ ∀ b, x.1.1 *ᵥ (fun i => (Q.map f) i (Sum.inr b)) = fun i => (Q.map f) i (Sum.inr b)`. Introduce `x`.

Establish `hcol : ∀ b, (fun i => (Q.map f) i (Sum.inr b)) = incl X.B.I (fun i => Q i (Sum.inr b))` using `fun _ => rfl`. Establish `ce : ∀ a, (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a` using `fun a => funext fun i => hQe a i`. Establish `cf : ∀ a, (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a` using `fun a => funext fun i => hQf a i`. Establish `cz : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u` using `funext fun i => hQz i`. Use `show (∀ y ∈ fixSet X u, X.B.I.fmat x *ᵥ incl X.B.I y = incl X.B.I y) ↔ _`.

Prove the components needed by the constructor for the conclusion. Introduce `hx b`. Rewrite using `[hcol]`. Apply `hx` to reduce the goal to its premises. Simplify using `only [fixSet, Set.mem_union, Set.mem_range, Set.mem_singleton_iff]`.

Break down `b with a | a | ⟨⟩` into its components or cases. Rewrite using `[ce]`. Conclude with `Or.inl (Or.inl ⟨a, rfl⟩)`. Rewrite using `[cf]`. Conclude with `Or.inl (Or.inr ⟨a, rfl⟩)`.

Rewrite using `[cz]`. Conclude with `Or.inr rfl`. Introduce `hx y hy`. Simplify using `only [fixSet, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hy`. Break down `hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl` into its components or cases.

Establish `h4` using `hx (Sum.inl a)`. Rewrite `h4` using `[hcol, ce]`. Then use the resulting hypothesis. Establish `h4` using `hx (Sum.inr (Sum.inl a))`. Rewrite `h4` using `[hcol, cf]`. Then use the resulting hypothesis. Establish `h4` using `hx (Sum.inr (Sum.inr ()))`.

Rewrite `h4` using `[hcol, cz]`. Then use the resulting hypothesis. Take `⟨Φ, hΦ⟩` from `frame_stabiliser_mulEquiv (Q := Q.map f) (Qi := Qi.map f) (sigA X.B.I) (Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ιA hσ (X.B.I.J.map f) (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).map f) (G'.map f) hA1 hA2 hDA hGA ( …`. Use `⟨Φ, fun h y => ?_⟩` and prove the remaining obligations. Rewrite using `[← hΦ h y]`. Establish `hq : ∀ j, qA X wt j = fun l => (Q.map f) l (Sum.inl j)`.

Introduce `j`. Use function extensionality and compare the values at `l`. Use `show f (X.crd (qFr wt j) l) = f (Q l (Sum.inl j))`. Rewrite using `[hQl]`. Use `show (∀ j, X.B.I.fmat (h : X.B.I.Gf) *ᵥ qA X wt j = ∑ i, ιA.symm (y.1.1 i j) • qA X wt i) ↔ _`.

Simplify using `only [hq]`.
-/
theorem frame_action_mulEquiv : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), WittX X u wt → IsAdeleIso X ιA → (∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a)) → ∃ (Φ : Hfin X u ≃* Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ (h : Hfin X u) y, RepF X wt ιA (h : X.B.I.Gf) y ↔ Φ h = y) := by
  intro D X u wt ιA hW hA hσ
  obtain ⟨Q, Qi, G', h1, h2, hQl, hQe, hQf, hQz, hG', hD⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW
  set f : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) with hf
  have hA1 : Q.map f * Qi.map f = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)]
  have hA2 : Qi.map f * Q.map f = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)]
  have hsf : ∀ x, sigA X.B.I (f x) = f (star x) := by
    intro x
    simp only [hf, sigA, Formalism.UG.sigR, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have hDA : ((Q.map f).map (sigA X.B.I))ᵀ * X.B.I.J.map f * Q.map f =
      Matrix.fromBlocks (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).map f) 0 0 (G'.map f) := by
    have hs : (Q.map f).map (sigA X.B.I) = (Q.map (starRingEnd X.B.I.E)).map f := by
      ext i j
      exact hsf (Q i j)
    rw [hs, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hD, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero f), Matrix.map_zero _ (map_zero f)]
  have hGA : IsUnit (G'.map f).det := by
    have h3 := hG'.map f
    rwa [RingHom.map_det] at h3
  have hGm : (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).map f).map ιA =
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map
        (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [hf, hA.1, RingEquiv.apply_symm_apply]
  have hH : ∀ x : X.B.I.Gf, x ∈ Hfin X u ↔
      ∀ b, x.1.1 *ᵥ (fun i => (Q.map f) i (Sum.inr b)) = fun i => (Q.map f) i (Sum.inr b) := by
    intro x
    have hcol : ∀ b, (fun i => (Q.map f) i (Sum.inr b)) = incl X.B.I (fun i => Q i (Sum.inr b)) :=
      fun _ => rfl
    have ce : ∀ a, (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := fun a => funext fun i => hQe a i
    have cf : ∀ a, (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a :=
      fun a => funext fun i => hQf a i
    have cz : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext fun i => hQz i
    show (∀ y ∈ fixSet X u, X.B.I.fmat x *ᵥ incl X.B.I y = incl X.B.I y) ↔ _
    constructor
    · intro hx b
      rw [hcol]
      apply hx
      simp only [fixSet, Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
      rcases b with a | a | ⟨⟩
      · rw [ce]; exact Or.inl (Or.inl ⟨a, rfl⟩)
      · rw [cf]; exact Or.inl (Or.inr ⟨a, rfl⟩)
      · rw [cz]; exact Or.inr rfl
    · intro hx y hy
      simp only [fixSet, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hy
      rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl
      · have h4 := hx (Sum.inl a)
        rwa [hcol, ce] at h4
      · have h4 := hx (Sum.inr (Sum.inl a))
        rwa [hcol, cf] at h4
      · have h4 := hx (Sum.inr (Sum.inr ()))
        rwa [hcol, cz] at h4
  obtain ⟨Φ, hΦ⟩ := frame_stabiliser_mulEquiv (Q := Q.map f) (Qi := Qi.map f) (sigA X.B.I)
    (Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ιA hσ
    (X.B.I.J.map f) (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).map f) (G'.map f)
    hA1 hA2 hDA hGA (Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F)) (fun _ => Iff.rfl)
    (Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (fun g => by rw [hGm]; exact Iff.rfl) (Hfin X u) hH
  refine ⟨Φ, fun h y => ?_⟩
  rw [← hΦ h y]
  have hq : ∀ j, qA X wt j = fun l => (Q.map f) l (Sum.inl j) := by
    intro j
    funext l
    show f (X.crd (qFr wt j) l) = f (Q l (Sum.inl j))
    rw [hQl]
  show (∀ j, X.B.I.fmat (h : X.B.I.Gf) *ᵥ qA X wt j = ∑ i, ιA.symm (y.1.1 i j) • qA X wt i) ↔ _
  simp only [hq]

end GlobalTheory
