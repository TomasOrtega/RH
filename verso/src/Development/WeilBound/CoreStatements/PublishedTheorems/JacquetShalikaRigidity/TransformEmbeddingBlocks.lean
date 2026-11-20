import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquiv

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace TransformEmbeddingBlocks

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Proceed by induction on `d generalizing f with`. Consider the case `zero => rfl`. Consider the case `succ d ih => show pT ψ j (d + 1) (colT ψ (j + (d + 1)) f) = colT ψ j (pT ψ (j + 1) d (colT ψ (j + 1 + d) f))`. Rewrite using `[ih, show j + 1 + d = j + (d + 1) by omega]`.
-/
theorem pT_succ' (ψ : AddChar (Ad E) ℂ) {a : ℕ} (j d : ℕ) (f : GA E a → ℂ) :
    pT ψ j (d + 1) f = colT ψ j (pT ψ (j + 1) d f) := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih =>
    show pT ψ j (d + 1) (colT ψ (j + (d + 1)) f) = colT ψ j (pT ψ (j + 1) d (colT ψ (j + 1 + d) f))
    rw [ih, show j + 1 + d = j + (d + 1) by omega]

/- English proof (translation)
Proceed by induction on `d generalizing f with`. Consider the case `zero => rfl`. Consider the case `succ d ih => show whit ψ (i + d) (colT ψ (i + d + 1) f) = whit ψ i (pT ψ (i + 1) d (colT ψ (i + 1 + d) f))`. Rewrite using `[ih, show i + 1 + d = i + d + 1 by omega]`.
-/
theorem whit_pT (ψ : AddChar (Ad E) ℂ) {a : ℕ} (i d : ℕ) (f : GA E a → ℂ) :
    whit ψ (i + d) f = whit ψ i (pT ψ (i + 1) d f) := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih =>
    show whit ψ (i + d) (colT ψ (i + d + 1) f) = whit ψ i (pT ψ (i + 1) d (colT ψ (i + 1 + d) f))
    rw [ih, show i + 1 + d = i + d + 1 by omega]

/- English proof (translation)
Proceed by induction on `d generalizing f with`. Consider the case `zero => exact hf`. Consider the case `succ d ih => show Good ψ i (pT ψ (i + 1) d (colT ψ (i + 1 + d) f))`. Rewrite using `[show i + 1 + d = i + d + 1 by omega]`. Conclude with `ih _ (by omega) (GlobalTheory.CuspRep.Generic.good_colT (m := i + d) hψ h hf)`.
-/
theorem good_pT {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {a : ℕ} (i d : ℕ) (f : GA E a → ℂ)
    (h : i + d < a) (hf : Good ψ (i + d) f) : Good ψ i (pT ψ (i + 1) d f) := by
  induction d generalizing f with
  | zero => exact hf
  | succ d ih =>
    show Good ψ i (pT ψ (i + 1) d (colT ψ (i + 1 + d) f))
    rw [show i + 1 + d = i + d + 1 by omega]
    exact ih _ (by omega) (GlobalTheory.CuspRep.Generic.good_colT (m := i + d) hψ h hf)

/- English proof (translation)
Use `⟨fun i c h => ?_, fun i => ?_, fun i c _ => rfl⟩` and prove the remaining obligations. Conclude with `Matrix.one_apply_ne (ne_of_gt h)`. Conclude with `Matrix.one_apply_eq i`.
-/
theorem uu_one {a : ℕ} (j : ℕ) : UU j (1 : GA E a) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c _ => rfl⟩
  · exact Matrix.one_apply_ne (ne_of_gt h)
  · exact Matrix.one_apply_eq i

/- English proof (translation)
Take `⟨x1, x2, x3⟩` from `hx`. Take `⟨y1, y2, y3⟩` from `hy`. Use `⟨fun i c h => ?_, fun i => ?_, fun i c h => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations.

Break down `lt_or_ge l i with hl | hl` into its components or cases. Rewrite using `[x1 i l hl, zero_mul]`. Rewrite using `[y1 l c (lt_of_lt_of_le h hl), mul_zero]`. Rewrite using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, x2, y2, one_mul]`. Introduce `l _ hl`.

Break down `lt_or_gt_of_ne hl with hl | hl` into its components or cases. Rewrite using `[x1 i l hl, zero_mul]`. Rewrite using `[y1 l i hl, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single c, y3 c c h, x3 i c h, Matrix.one_apply_eq, mul_one]`.

Introduce `l _ hl`. Rewrite using `[y3 l c h, Matrix.one_apply_ne hl, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem uu_mul {a j : ℕ} {x y : GA E a} (hx : UU j x) (hy : UU j y) : UU j (x * y) := by
  obtain ⟨x1, x2, x3⟩ := hx
  obtain ⟨y1, y2, y3⟩ := hy
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with hl | hl
    · rw [x1 i l hl, zero_mul]
    · rw [y1 l c (lt_of_lt_of_le h hl), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, x2, y2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hl | hl
      · rw [x1 i l hl, zero_mul]
      · rw [y1 l i hl, mul_zero]
    · simp
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single c, y3 c c h, x3 i c h, Matrix.one_apply_eq, mul_one]
    · intro l _ hl
      rw [y3 l c h, Matrix.one_apply_ne hl, mul_zero]
    · simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i c = _`. Rewrite using `[Matrix.add_apply, posM, Matrix.sum_apply]`. Simplify using `only [Matrix.single_apply]`.
-/
theorem blkU_apply {R : Type} [CommRing R] {a r n : ℕ} (x : UnipotentBlockColumnIndex a r n → R) (i c : Fin a) :
    (blkU x).val i c = (1 : Matrix (Fin a) (Fin a) R) i c + ∑ t, if t.1.1 = i ∧ t.1.2 = c then x t else 0 := by
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i c = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply]
  simp only [Matrix.single_apply]

/- English proof (translation)
Rewrite using `[blkU_apply, Finset.sum_eq_zero, add_zero]`. Introduce `t _`. Rewrite using `[if_neg (h t)]`.
-/
theorem blkU_apply_of {R : Type} [CommRing R] {a r n : ℕ} (x : UnipotentBlockColumnIndex a r n → R) (i c : Fin a)
    (h : ∀ t : UnipotentBlockColumnIndex a r n, ¬ (t.1.1 = i ∧ t.1.2 = c)) :
    (blkU x).val i c = (1 : Matrix (Fin a) (Fin a) R) i c := by
  rw [blkU_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  rw [if_neg (h t)]

/- English proof (translation)
Use `⟨fun r c h => ?_, fun r => ?_, fun r c h => ?_⟩` and prove the remaining obligations. Rewrite using `[blkU_apply_of _ _ _ ?_, Matrix.one_apply_ne (ne_of_gt h)]`. Introduce and unpack `t ⟨e1, e2⟩`. Use `t.2` as an intermediate fact. Substitute `e1 e2` using the available equality.

Rewrite `h` using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[blkU_apply_of _ _ _ ?_, Matrix.one_apply_eq]`. Introduce and unpack `t ⟨e1, e2⟩`. Use `t.2` as an intermediate fact.

Establish `e3 : (t.1.1 : ℕ) = t.1.2` using `by rw [e1, e2]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[blkU_apply_of _ _ _ ?_]`. Introduce and unpack `t ⟨e1, e2⟩`. Use `t.2` as an intermediate fact.

Substitute `e1 e2` using the available equality. Use linear arithmetic over natural numbers and integers.
-/
theorem uu_blkU {a j i : ℕ} (hj : j ≤ i) (y : UnipotentBlockColumnIndex a i i → Ad E) : UU j (blkU y : GA E a) := by
  refine ⟨fun r c h => ?_, fun r => ?_, fun r c h => ?_⟩
  · rw [blkU_apply_of _ _ _ ?_, Matrix.one_apply_ne (ne_of_gt h)]
    rintro t ⟨e1, e2⟩
    have := t.2
    subst e1 e2
    rw [Fin.lt_def] at h
    omega
  · rw [blkU_apply_of _ _ _ ?_, Matrix.one_apply_eq]
    rintro t ⟨e1, e2⟩
    have := t.2
    have e3 : (t.1.1 : ℕ) = t.1.2 := by rw [e1, e2]
    omega
  · rw [blkU_apply_of _ _ _ ?_]
    rintro t ⟨e1, e2⟩
    have := t.2
    subst e1 e2
    omega

/- English proof (translation)
Set `_ : MeasurableSpace G` to `borel G`. Unfold `avg`. Use `split_ifs with hp`. Take `⟨-, -, h1⟩` from `hp.choose_spec`. Use `norm_setIntegral_le_of_norm_le_const (μ := hp.choose.1) (s := hp.choose.2) (f := Φ) (C := B) (by rw [h1]; exact ENNReal.one_lt_top) (fun x _ => h x)` as an intermediate fact.

Rewrite `this` using `[Measure.real, h1, ENNReal.toReal_one, mul_one]`. Then use the resulting hypothesis. Simplify using `using hB`.
-/
theorem norm_avg_le {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G) (Φ : G → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ x, ‖Φ x‖ ≤ B) : ‖avg Γ Φ‖ ≤ B := by
  let _ : MeasurableSpace G := borel G
  unfold avg
  split_ifs with hp
  · obtain ⟨-, -, h1⟩ := hp.choose_spec
    have := norm_setIntegral_le_of_norm_le_const (μ := hp.choose.1) (s := hp.choose.2) (f := Φ) (C := B)
      (by rw [h1]; exact ENNReal.one_lt_top) (fun x _ => h x)
    rwa [Measure.real, h1, ENNReal.toReal_one, mul_one] at this
  · simpa using hB

/- English proof (translation)
Unfold `colT coefF`. Use `norm_avg_le _ _ hB fun y => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hψ.norm, one_mul]`. Conclude with `h y`.
-/
theorem norm_colT_le {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {a : ℕ} (n : ℕ) (f : GA E a → ℂ) (x : GA E a) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ y : UnipotentBlockColumnIndex a n n → Ad E, ‖f (blkU y * x)‖ ≤ B) : ‖colT ψ n f x‖ ≤ B := by
  unfold colT coefF
  refine norm_avg_le _ _ hB fun y => ?_
  rw [norm_mul, hψ.norm, one_mul]
  exact h y

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => exact fun f hf => hf`. Consider the case `succ d ih`. Introduce `f hf`. Use `ih _ fun u hu => ?_` and prove the remaining obligations.

Establish `hB : 0 ≤ B` using `(norm_nonneg _).trans (hf 1 (uu_one j))`. Use `norm_colT_le hψ _ _ _ hB fun y => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Conclude with `hf _ (uu_mul (uu_blkU (by omega) y) hu)`.
-/
theorem bound_pT {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {a : ℕ} (j : ℕ) (x : GA E a) (B : ℝ) (d : ℕ) :
    ∀ f : GA E a → ℂ, (∀ u, UU j u → ‖f (u * x)‖ ≤ B) → ∀ u, UU j u → ‖pT ψ j d f (u * x)‖ ≤ B := by
  induction d with
  | zero => exact fun f hf => hf
  | succ d ih =>
    intro f hf
    refine ih _ fun u hu => ?_
    have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1 (uu_one j))
    refine norm_colT_le hψ _ _ _ hB fun y => ?_
    rw [← mul_assoc]
    exact hf _ (uu_mul (uu_blkU (by omega) y) hu)

/- English proof (translation)
Introduce `i c h`. Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Break down `h with h | h` into its components or cases. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[hx i i (Or.inl h), Matrix.one_apply_eq, one_mul, hy i c (Or.inl h)]`.

Introduce `l _ hl`. Rewrite using `[hx i l (Or.inl h), Matrix.one_apply_ne (Ne.symm hl), zero_mul]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_single c]`. Rewrite using `[hy c c (Or.inr h), Matrix.one_apply_eq, mul_one, hx i c (Or.inr h)]`.

Introduce `l _ hl`. Rewrite using `[hy l c (Or.inr h), Matrix.one_apply_ne hl, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem mir_mul {R : Type} [CommRing R] {a n : ℕ} {x y : GL (Fin a) R} (hx : Mir n x) (hy : Mir n y) :
    Mir n (x * y) := by
  intro i c h
  rw [Units.val_mul, Matrix.mul_apply]
  rcases h with h | h
  · rw [Finset.sum_eq_single i]
    · rw [hx i i (Or.inl h), Matrix.one_apply_eq, one_mul, hy i c (Or.inl h)]
    · intro l _ hl
      rw [hx i l (Or.inl h), Matrix.one_apply_ne (Ne.symm hl), zero_mul]
    · simp
  · rw [Finset.sum_eq_single c]
    · rw [hy c c (Or.inr h), Matrix.one_apply_eq, mul_one, hx i c (Or.inr h)]
    · intro l _ hl
      rw [hy l c (Or.inr h), Matrix.one_apply_ne hl, mul_zero]
    · simp

/- English proof (translation)
Introduce `i c h`. Apply `blkU_apply_of` to reduce the goal to its premises. Introduce and unpack `t ⟨e1, e2⟩`. Use `t.2` as an intermediate fact. Substitute `e1 e2` using the available equality.

Use linear arithmetic over natural numbers and integers.
-/
theorem mir_blkU {R : Type} [CommRing R] {a j n : ℕ} (hj : j ≤ n) (y : UnipotentBlockColumnIndex a j j → R) : Mir n (blkU y) := by
  intro i c h
  apply blkU_apply_of
  rintro t ⟨e1, e2⟩
  have := t.2
  subst e1 e2
  omega

/- English proof (translation)
Introduce `i c hic`. Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) (γ.val i c) = _`. Rewrite using `[h i c hic, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mir_ratGL {a n : ℕ} (γ : GL (Fin a) E) (h : IsMir n γ) : Mir n (ratGL E a γ) := by
  intro i c hic
  change algebraMap E (Ad E) (γ.val i c) = _
  rw [h i c hic, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

omit [NumberField E] in
/- English proof (translation)
Introduce `i c hic`. Rewrite using `[hιE, embM, Matrix.of_apply]`. Use `split_ifs with h2`. Rewrite using `[h ⟨i, h2.1⟩ ⟨c, h2.2⟩ hic]`. Simplify using `[Matrix.one_apply, Fin.ext_iff]`.

Both sides reduce to the same expression.
-/
theorem isMir_emb {k m n : ℕ} (ιE : GL (Fin k) E →* GL (Fin m) E) (hιE : IsEmb ιE) (γ : GL (Fin k) E)
    (h : IsMir n γ) : IsMir n (ιE γ) := by
  intro i c hic
  rw [hιE, embM, Matrix.of_apply]
  split_ifs with h2
  · rw [h ⟨i, h2.1⟩ ⟨c, h2.2⟩ hic]
    simp [Matrix.one_apply, Fin.ext_iff]
  · rfl

/- English proof (translation)
Take `⟨q, rfl⟩` from `hs x fun i c h => hx i c (by omega)`. Use `⟨q, fun i c h => ?_, rfl⟩` and prove the remaining obligations. Establish `h1` using `hx (Fin.castLE hkm i) (Fin.castLE hkm c) (by simpa using h)`. Rewrite `h1` using `[hι, embM, Matrix.of_apply, dif_pos ⟨i.2, c.2⟩]`. Apply the tactic sequence `convert h1 using 1 <;> first | rfl | (rw [Matrix.one_apply, Matrix.one_apply]; simp only [Fin.ext_iff, Fin.val_castLE])`.
-/
theorem mir_emb {m n : ℕ} (hkm : n + 1 ≤ m) (ι : GA E (n + 1) →* GA E m) (hι : IsEmb ι)
    (hs : ∀ x : GA E m, GlobalTheory (n + 1) x → ∃ g, x = ι g) (x : GA E m) (hx : Mir n x) :
    ∃ q, Mir n q ∧ x = ι q := by
  obtain ⟨q, rfl⟩ := hs x fun i c h => hx i c (by omega)
  refine ⟨q, fun i c h => ?_, rfl⟩
  have h1 := hx (Fin.castLE hkm i) (Fin.castLE hkm c) (by simpa using h)
  rw [hι, embM, Matrix.of_apply, dif_pos ⟨i.2, c.2⟩] at h1
  convert h1 using 1 <;> first | rfl | (rw [Matrix.one_apply, Matrix.one_apply]; simp only [Fin.ext_iff, Fin.val_castLE])

/- English proof (translation)
The claim follows from `posU_zero _`.
-/
theorem blkU_zero' {a j : ℕ} : (blkU (0 : UnipotentBlockColumnIndex a j j → Ad E) : GA E a) = 1 := posU_zero _

def sig {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) : UnipotentBlockColumnIndex k j j ≃ UnipotentBlockColumnIndex m j j where
  toFun t := ⟨(Fin.castLE hkm t.1.1, Fin.castLE hkm t.1.2), t.2⟩
  invFun t := ⟨(⟨t.1.1, by have := t.2; omega⟩, ⟨t.1.2, by have := t.2; omega⟩), t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem sig_fst {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (t : UnipotentBlockColumnIndex k j j) :
    ((sig hkm hj t).1.1 : ℕ) = t.1.1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem sig_snd {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (t : UnipotentBlockColumnIndex k j j) :
    ((sig hkm hj t).1.2 : ℕ) = t.1.2 := rfl

def eqv {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) : (UnipotentBlockColumnIndex k j j → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex m j j → Ad E) where
  toFun x t := x ((sig hkm hj).symm t)
  invFun y t := y (sig hkm hj t)
  left_inv x := by funext t; simp
  right_inv y := by funext t; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eqv_apply {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (x : UnipotentBlockColumnIndex k j j → Ad E) :
    eqv hkm hj x = fun t => x ((sig hkm hj).symm t) := rfl

/- English proof (translation)
Simplify using `only [ratV, AddMonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Use `⟨fun t => c (sig hkm hj t), funext fun t => ?_⟩` and prove the remaining obligations. Use `congrFun hc (sig hkm hj t)` as an intermediate fact.

Simplify `this` using `[eqv_apply]`. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨fun t => c ((sig hkm hj).symm t), rfl⟩`.
-/
theorem mem_eqv {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (x : UnipotentBlockColumnIndex k j j → Ad E) :
    eqv hkm hj x ∈ ratV E (UnipotentBlockColumnIndex m j j) ↔ x ∈ ratV E (UnipotentBlockColumnIndex k j j) := by
  simp only [ratV, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun t => c (sig hkm hj t), funext fun t => ?_⟩
    have := congrFun hc (sig hkm hj t)
    simpa [eqv_apply] using this
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c ((sig hkm hj).symm t), rfl⟩

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i c`. Rewrite using `[hι, embM, Matrix.of_apply]`. Use `split_ifs with h`. Rewrite using `[blkU_apply, blkU_apply]`.

Use `congr 1`. Simplify using `[Matrix.one_apply, Fin.ext_iff]`. Use `Fintype.sum_equiv (sig hkm hj) _ _ fun t => ?_` and prove the remaining obligations. Simplify using `[Fin.ext_iff]`. Use `symm`.

Apply `blkU_apply_of` to reduce the goal to its premises. Introduce and unpack `t ⟨e1, e2⟩`. Apply `h` to reduce the goal to its premises. Use `t.2` as an intermediate fact. Substitute `e1 e2` using the available equality.

Use linear arithmetic over natural numbers and integers.
-/
theorem emb_blkU {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (ι : GA E k →* GA E m) (hι : IsEmb ι)
    (x : UnipotentBlockColumnIndex k j j → Ad E) : ι (blkU x) = blkU (fun t => x ((sig hkm hj).symm t)) := by
  apply Units.ext
  ext i c
  rw [hι, embM, Matrix.of_apply]
  split_ifs with h
  · rw [blkU_apply, blkU_apply]
    congr 1
    · simp [Matrix.one_apply, Fin.ext_iff]
    · refine Fintype.sum_equiv (sig hkm hj) _ _ fun t => ?_
      simp [Fin.ext_iff]
  · symm
    apply blkU_apply_of
    rintro t ⟨e1, e2⟩
    apply h
    have := t.2
    subst e1 e2
    omega

/- English proof (translation)
Unfold `dot`. Use `(Fintype.sum_equiv (sig hkm hj) _ _ fun t => ?_).symm` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem dot_eqv {k m j : ℕ} (hkm : k ≤ m) (hj : j < k) (x : UnipotentBlockColumnIndex k j j → Ad E) :
    dot (eLast m j) (fun t => x ((sig hkm hj).symm t)) = dot (eLast k j) x := by
  unfold dot
  refine (Fintype.sum_equiv (sig hkm hj) _ _ fun t => ?_).symm
  beta_reduce
  rw [Equiv.symm_apply_apply]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `colT coefF`. Use `Eq.trans ?_ (avg_equiv _ _ _ _ (isCoLat_ratV E _) (isCoLat_ratV E _) (eqv hkm hj) (mem_eqv hkm hj) _ (per_coef hψ (eLast m j) hG.cont (GlobalTheory.CuspRep.Generic.hl_of_good hG le_rfl) (ι g)))` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[eqv_apply, dot_eqv]`. Use `beta_reduce`. Rewrite using `[map_mul, emb_blkU hkm hj ι hι]`.
-/
theorem colT_emb {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {k m j : ℕ} (hkm : k ≤ m) (hj : j < k)
    (ι : GA E k →* GA E m) (hι : IsEmb ι) (G : GA E m → ℂ) (hG : Good ψ j G) :
    colT ψ j (fun g => G (ι g)) = fun g => colT ψ j G (ι g) := by
  funext g
  unfold colT coefF
  refine Eq.trans ?_ (avg_equiv _ _ _ _ (isCoLat_ratV E _) (isCoLat_ratV E _) (eqv hkm hj) (mem_eqv hkm hj) _
    (per_coef hψ (eLast m j) hG.cont (GlobalTheory.CuspRep.Generic.hl_of_good hG le_rfl) (ι g)))
  congr 1
  funext x
  rw [eqv_apply, dot_eqv]
  beta_reduce
  rw [map_mul, emb_blkU hkm hj ι hι]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro _ G _`. Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `hn G hG`.

Rewrite using `[whit_succ, whit_succ, colT_emb hψ hkm.le hn ι hι G hG]`. Conclude with `ih (by omega) _ (GlobalTheory.CuspRep.Generic.good_colT hψ (by omega) hG)`.
-/
theorem whit_emb {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {k m : ℕ} (hkm : k < m) (ι : GA E k →* GA E m)
    (hι : IsEmb ι) (n : ℕ) : n < k → ∀ G : GA E m → ℂ, Good ψ n G →
      whit ψ n (fun g => G (ι g)) = fun g => whit ψ n G (ι g) := by
  induction n with
  | zero => intro _ G _; rfl
  | succ n ih =>
    intro hn G hG
    rw [whit_succ, whit_succ, colT_emb hψ hkm.le hn ι hι G hG]
    exact ih (by omega) _ (GlobalTheory.CuspRep.Generic.good_colT hψ (by omega) hG)

end TransformEmbeddingBlocks

/- English proof (translation)
Introduce `hG11 _ _ _ hK5e E _ _ _ m k hk hkm ψ hψ ι hι φ hφ`. Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`. Take `⟨hR, hE⟩` from `hK5e E m (n + 1) hkm.le`. Take `⟨hcont, -, hsurj, -, -, -, hrat, -⟩` from `hE ι hι`. Take `⟨ιE, hιE⟩` from `hR E`.

Establish `hm1 : n + (m - (n + 1)) = m - 1` using `by omega`. Establish `hgood1 : Good ψ (n + 1) (pT ψ (n + 1 + 1) (m - (n + 1 + 1)) φ)`. Use `TransformEmbeddingBlocks.good_pT hψ (n + 1) (m - (n + 1 + 1)) φ (by omega) ?_` and prove the remaining obligations. Rewrite using `[show n + 1 + (m - (n + 1 + 1)) = m - 1 by omega]` and apply the resulting hypothesis. Establish `hgood0 : Good ψ n (pT ψ (n + 1) (m - (n + 1)) φ)`.

Use `TransformEmbeddingBlocks.good_pT hψ n _ φ (by omega) ?_` and prove the remaining obligations. Rewrite using `[hm1]` and apply the resulting hypothesis. Establish `hwhit : whit ψ (m - 1) φ = whit ψ n (pT ψ (n + 1) (m - (n + 1)) φ)`. Rewrite using `[← TransformEmbeddingBlocks.whit_pT, hm1]`. Establish `hwe` using `TransformEmbeddingBlocks.whit_emb hψ hkm ι hι n (by omega) _ hgood0`.

Use `⟨hgood1, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show m - (n + 1) = m - (n + 1 + 1) + 1 by omega, TransformEmbeddingBlocks.pT_succ']`. Use `show Pre ψ n _`. Use `⟨hgood0.cont.comp hcont, fun γ hγ g => ?_, fun j hj y g => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hrat ιE hιE γ]`.

Conclude with `hgood0.left _ (TransformEmbeddingBlocks.isMir_emb ιE hιE γ hγ) _`. Establish `: IsEmpty (UnipotentBlockColumnIndex (n + 1) j j)` using `⟨fun t => by have := t.2; have := t.1.2.2; omega⟩`. Take `rfl : y = 0` from `funext fun t => isEmptyElim t`. Rewrite using `[TransformEmbeddingBlocks.blkU_zero', one_mul]`. Simplify using `[dot]`.

Introduce `g show whit ψ n _ g = _`. Rewrite using `[hwe, hwhit]`. Introduce `g hg`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Apply `hg` to reduce the goal to its premises. Establish `key` using `hG11 E m ψ hψ n (pT ψ (n + 1) (m - (n + 1)) φ) (Or.inl (by omega)) hgood0 {x | ∃ p : GA E (n + 1), Mir n p ∧ x = ι (p * g)} ?_ ?_ ?_ (ι g) ⟨1, fun i c _ => rfl, by rw [one_mul]⟩`. Conclude with `key`. Introduce and unpack `γ hγ _ ⟨p, hp, rfl⟩`. Take `⟨q, hq, hq'⟩` from `TransformEmbeddingBlocks.mir_emb hkm.le ι hι hsurj _ (TransformEmbeddingBlocks.mir_ratGL γ hγ)`.

Conclude with `⟨q * p, TransformEmbeddingBlocks.mir_mul hq hp, by rw [hq', ← map_mul, mul_assoc]⟩`. Introduce and unpack `j hj y _ ⟨p, hp, rfl⟩`. Take `⟨q, hq, hq'⟩` from `TransformEmbeddingBlocks.mir_emb hkm.le ι hι hsurj _ (TransformEmbeddingBlocks.mir_blkU hj y)`. Conclude with `⟨q * p, TransformEmbeddingBlocks.mir_mul hq hp, by rw [hq', ← map_mul, mul_assoc]⟩`. Introduce and unpack `_ ⟨p, hp, rfl⟩`.

Rewrite using `[← hwhit]`. Conclude with `hne p hp`. Introduce `j x B hj hjm hB`. Use `TransformEmbeddingBlocks.bound_pT hψ j x B (m - j) φ hB 1 (TransformEmbeddingBlocks.uu_one j)` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem transform_embedding_of : jumpWindows.FourierUniquenessMirabolic → P0 → P1 → P2 → CornerEmbedding → TransformsEmbedding := by
  intro hG11 _ _ _ hK5e E _ _ _ m k hk hkm ψ hψ ι hι φ hφ
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hR, hE⟩ := hK5e E m (n + 1) hkm.le
  obtain ⟨hcont, -, hsurj, -, -, -, hrat, -⟩ := hE ι hι
  obtain ⟨ιE, hιE⟩ := hR E
  have hm1 : n + (m - (n + 1)) = m - 1 := by omega
  have hgood1 : Good ψ (n + 1) (pT ψ (n + 1 + 1) (m - (n + 1 + 1)) φ) := by
    refine TransformEmbeddingBlocks.good_pT hψ (n + 1) (m - (n + 1 + 1)) φ (by omega) ?_
    rwa [show n + 1 + (m - (n + 1 + 1)) = m - 1 by omega]
  have hgood0 : Good ψ n (pT ψ (n + 1) (m - (n + 1)) φ) := by
    refine TransformEmbeddingBlocks.good_pT hψ n _ φ (by omega) ?_
    rwa [hm1]
  have hwhit : whit ψ (m - 1) φ = whit ψ n (pT ψ (n + 1) (m - (n + 1)) φ) := by
    rw [← TransformEmbeddingBlocks.whit_pT, hm1]
  have hwe := TransformEmbeddingBlocks.whit_emb hψ hkm ι hι n (by omega) _ hgood0
  refine ⟨hgood1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show m - (n + 1) = m - (n + 1 + 1) + 1 by omega, TransformEmbeddingBlocks.pT_succ']
  · show Pre ψ n _
    refine ⟨hgood0.cont.comp hcont, fun γ hγ g => ?_, fun j hj y g => ?_⟩
    · rw [map_mul, hrat ιE hιE γ]
      exact hgood0.left _ (TransformEmbeddingBlocks.isMir_emb ιE hιE γ hγ) _
    · have : IsEmpty (UnipotentBlockColumnIndex (n + 1) j j) := ⟨fun t => by have := t.2; have := t.1.2.2; omega⟩
      obtain rfl : y = 0 := funext fun t => isEmptyElim t
      rw [TransformEmbeddingBlocks.blkU_zero', one_mul]
      simp [dot]
  · intro g
    show whit ψ n _ g = _
    rw [hwe, hwhit]
  · intro g hg
    by_contra hne
    push Not at hne
    apply hg
    have key := hG11 E m ψ hψ n (pT ψ (n + 1) (m - (n + 1)) φ) (Or.inl (by omega)) hgood0
      {x | ∃ p : GA E (n + 1), Mir n p ∧ x = ι (p * g)} ?_ ?_ ?_ (ι g) ⟨1, fun i c _ => rfl, by rw [one_mul]⟩
    · exact key
    · rintro γ hγ _ ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hq'⟩ := TransformEmbeddingBlocks.mir_emb hkm.le ι hι hsurj _ (TransformEmbeddingBlocks.mir_ratGL γ hγ)
      exact ⟨q * p, TransformEmbeddingBlocks.mir_mul hq hp, by rw [hq', ← map_mul, mul_assoc]⟩
    · rintro j hj y _ ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hq'⟩ := TransformEmbeddingBlocks.mir_emb hkm.le ι hι hsurj _ (TransformEmbeddingBlocks.mir_blkU hj y)
      exact ⟨q * p, TransformEmbeddingBlocks.mir_mul hq hp, by rw [hq', ← map_mul, mul_assoc]⟩
    · rintro _ ⟨p, hp, rfl⟩
      rw [← hwhit]
      exact hne p hp
  · intro j x B hj hjm hB
    have := TransformEmbeddingBlocks.bound_pT hψ j x B (m - j) φ hB 1 (TransformEmbeddingBlocks.uu_one j)
    rwa [one_mul] at this

end PositivityTheory.AdelicQuotientData

end
