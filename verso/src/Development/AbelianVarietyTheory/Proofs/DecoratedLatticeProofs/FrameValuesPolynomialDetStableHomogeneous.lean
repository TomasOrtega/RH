import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStablStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KJInf.ValPol

variable {ι : Type} [Fintype ι] {a : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalAt_eq (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y F = MvPolynomial.eval (fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) F := rfl

/- English proof (translation)
Rewrite using `[evalAt_eq, Formalism.L2.Ker.frDet, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[RingHom.mapMatrix_apply]`.
-/
theorem evalAt_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    evalAt y (Formalism.L2.Ker.frDet ℂ a τ) = (y τ).det := by
  rw [evalAt_eq, Formalism.L2.Ker.frDet, RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply]

/- English proof (translation)
Rewrite using `[evalAt_eq, map_mul, map_prod, ← evalAt_eq]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, ← evalAt_eq, evalAt_frDet]`.
-/
theorem evalAt_mul_prod (y : ι → Matrix (Fin a) (Fin a) ℂ) (P : PY ι a) (n : ι → ℕ) :
    evalAt y (P * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ n τ) = evalAt y P * ∏ τ, (y τ).det ^ n τ := by
  rw [evalAt_eq, map_mul, map_prod, ← evalAt_eq]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, ← evalAt_eq, evalAt_frDet]

/- English proof (translation)
Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, one_mul, evalAt]`.
-/
theorem fnOf_one_apply {G : ι → Matrix (Fin a) (Fin a) ℂ} (s : ι → ℤ) (P : PY ι a) (y : Frames G) :
    fnOf G s 1 P y = (∏ τ, (y.1 τ).det ^ s τ) * evalAt y.1 P := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, one_mul, evalAt]

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C c => simp [evalAt, lft]`. Consider the case `add p q hp hq => simp only [evalAt, map_add] at *`. Rewrite using `[hp, hq]`. Consider the case `mul_X p v hp`.

Simplify using `only [evalAt, map_mul] at *`. Rewrite using `[hp]`. Simplify using `[lft, Matrix.mul_apply]`.
-/
theorem evalAt_lft (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [evalAt, lft]
  | add p q hp hq => simp only [evalAt, map_add] at *; rw [hp, hq]
  | mul_X p v hp =>
    simp only [evalAt, map_mul] at *
    rw [hp]
    simp [lft, Matrix.mul_apply]

/- English proof (translation)
Rewrite using `[evalAt_mul_prod, fnOf_one_apply, mul_assoc, mul_comm, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hd : (y.1 τ).det ≠ 0` using `(y.2 τ).ne_zero`. Rewrite using `[← zpow_natCast, ← zpow_add₀ hd, hns τ]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shift_eq {G : ι → Matrix (Fin a) (Fin a) ℂ} (lam : ι → DomWeight a) {n : ι → ℕ} {s : ι → ℤ}
    (hns : ∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) (P : PY ι a) (y : Frames G) :
    evalAt y.1 (P * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ n τ) * ∏ τ, (y.1 τ).det ^ (-s τ) =
      fnOf G (shiftOf lam) 1 P y := by
  rw [evalAt_mul_prod, fnOf_one_apply, mul_assoc, mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : (y.1 τ).det ≠ 0 := (y.2 τ).ne_zero
  rw [← zpow_natCast, ← zpow_add₀ hd, hns τ]
  congr 1
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, hP, rfl⟩`. Conclude with `⟨_, ⟨P, hP, rfl⟩, fun y => (shift_eq lam hns P y).symm⟩`. Introduce and unpack `⟨F, ⟨P, hP, rfl⟩, hΦ⟩`. Use `⟨P, hP, funext fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[hΦ y]`. Conclude with `(shift_eq lam hns P y).symm`.
-/
theorem mem_valC_iff (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (n : ι → ℕ) (s : ι → ℤ)
    (hns : ∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) (Φ : Frames G → ℂ) :
    Φ ∈ ValC G lam ↔ ∃ F ∈ Vn lam n, ∀ y, Φ y = evalAt y.1 F * ∏ τ, (y.1 τ).det ^ (-s τ) := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨_, ⟨P, hP, rfl⟩, fun y => (shift_eq lam hns P y).symm⟩
  · rintro ⟨F, ⟨P, hP, rfl⟩, hΦ⟩
    refine ⟨P, hP, funext fun y => ?_⟩
    rw [hΦ y]
    exact (shift_eq lam hns P y).symm

def nOf (lam : ι → DomWeight a) : ι → ℕ := fun τ => (shiftOf lam τ).toNat

def sOf (lam : ι → DomWeight a) : ι → ℤ := fun τ => (nOf lam τ : ℤ) - shiftOf lam τ

/- English proof (translation)
Simplify using `[sOf]`.
-/
theorem nOf_eq (lam : ι → DomWeight a) (τ : ι) : (nOf lam τ : ℤ) = shiftOf lam τ + sOf lam τ := by
  simp [sOf]

/- English proof (translation)
Use extensionality with `Φ`. Rewrite using `[mem_valC_iff G lam _ _ (nOf_eq lam)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨F, hF, hΦ⟩`. Use `⟨F, hF, funext fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[hΦ y, fnOf_one_apply, mul_comm]`. Introduce and unpack `⟨F, hF, rfl⟩`. Conclude with `⟨F, hF, fun y => by rw [fnOf_one_apply, mul_comm]⟩`.
-/
theorem valC_eq_map (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) :
    ValC G lam = (Vn lam (nOf lam)).map (fnOf G (fun τ => -sOf lam τ) 1) := by
  ext Φ
  rw [mem_valC_iff G lam _ _ (nOf_eq lam)]
  constructor
  · rintro ⟨F, hF, hΦ⟩
    refine ⟨F, hF, funext fun y => ?_⟩
    rw [hΦ y, fnOf_one_apply, mul_comm]
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, hF, fun y => by rw [fnOf_one_apply, mul_comm]⟩

/- English proof (translation)
Use `haveI := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam (nOf lam)).1`. Rewrite using `[valC_eq_map]`. Use `infer_instance`.
-/
theorem finiteDimensional_valC (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) :
    FiniteDimensional ℂ (ValC G lam) := by
  haveI := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam (nOf lam)).1
  rw [valC_eq_map]
  infer_instance

/- English proof (translation)
Take `⟨F, hF, hΦF⟩` from `(mem_valC_iff G lam _ _ (nOf_eq lam) Φ).1 hΦ`. Rewrite using `[mem_valC_iff G lam _ _ (nOf_eq lam)]`. Use `⟨(∏ τ, (g τ).det ^ (-sOf lam τ)) • lft g F, Submodule.smul_mem _ _ ((GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam (nOf lam)).2 g F hF), fun y => ?_⟩` and prove the remaining obligations. Set `y' : Frames G` to `⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩`. Rewrite using `[hΦ' y y' (fun τ => rfl), hΦF y']`.

Establish `e : evalAt y.1 ((∏ τ, (g τ).det ^ (-sOf lam τ)) • lft g F) = (∏ τ, (g τ).det ^ (-sOf lam τ)) * evalAt (fun τ => g τ * y.1 τ) F`. Rewrite using `[evalAt_eq, MvPolynomial.smul_eval, ← evalAt_eq, evalAt_lft]`. Rewrite using `[e]`. Simplify using `only [y', Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem valC_stable (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (Φ : Frames G → ℂ) (hΦ : Φ ∈ ValC G lam)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (Φ' : Frames G → ℂ) (hΦ' : ∀ y y', IsTr g y y' → Φ' y = Φ y') (hg : IsInv g) :
    Φ' ∈ ValC G lam := by
  obtain ⟨F, hF, hΦF⟩ := (mem_valC_iff G lam _ _ (nOf_eq lam) Φ).1 hΦ
  rw [mem_valC_iff G lam _ _ (nOf_eq lam)]
  refine ⟨(∏ τ, (g τ).det ^ (-sOf lam τ)) • lft g F,
    Submodule.smul_mem _ _ ((GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam (nOf lam)).2 g F hF), fun y => ?_⟩
  let y' : Frames G := ⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩
  rw [hΦ' y y' (fun τ => rfl), hΦF y']
  have e : evalAt y.1 ((∏ τ, (g τ).det ^ (-sOf lam τ)) • lft g F) =
      (∏ τ, (g τ).det ^ (-sOf lam τ)) * evalAt (fun τ => g τ * y.1 τ) F := by
    rw [evalAt_eq, MvPolynomial.smul_eval, ← evalAt_eq, evalAt_lft]
  rw [e]
  simp only [y', Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Introduce `i j h` and use `Int.toNat_le_toNat (by have := l.anti h; omega)`.
-/
theorem natW_anti' (l : DomWeight a) : Antitone l.natW := fun i j h =>
  Int.toNat_le_toNat (by have := l.anti h; omega)

/- English proof (translation)
Establish `h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f l.natW` using `(Formalism.GradedWeylDivisibility.weylLeDual ℂ a a le_rfl l.natW (natW_anti' l) hf).1`. Introduce `m hm`. Rewrite using `[← h hm]`. Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Formalism.GradedWeylDivisibility.colW]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `[Pi.single_apply]`.
-/
theorem isHomogeneous_of_mem_delSq (l : DomWeight a) {f : MvPolynomial (Fin a × Fin a) ℂ} (hf : f ∈ delSq ℂ a l) :
    f.IsHomogeneous (∑ r, l.natW r) := by
  have h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f l.natW :=
    (Formalism.GradedWeylDivisibility.weylLeDual ℂ a a le_rfl l.natW (natW_anti' l) hf).1
  intro m hm
  rw [← h hm]
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Formalism.GradedWeylDivisibility.colW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply]

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `: m.degree = d`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `hf (MvPolynomial.mem_support_iff.1 hm)`.

Rewrite using `[← this, Finsupp.degree_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_smul_of_isHomogeneous {σ : Type} {f : MvPolynomial σ ℂ} {d : ℕ} (hf : f.IsHomogeneous d)
    (c : ℂ) (v : σ → ℂ) : MvPolynomial.eval (c • v) f = c ^ d * MvPolynomial.eval v f := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (MvPolynomial.mem_support_iff.1 hm)
  rw [← this, Finsupp.degree_apply]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/- English proof (translation)
Establish `h : ∀ i, ((l.natW i : ℕ) : ℤ) = l.w i - l.detShift`. Introduce `i`. Establish `hpos : 0 < a` using `Fin.pos i`. Establish `hle : l.w ⟨a - 1, by omega⟩ ≤ l.w i` using `l.anti (Fin.le_iff_val_le_val.2 (by simp; omega))`. Simplify using `only [DomWeight.natW, DomWeight.detShift, dif_pos hpos]`.

Conclude with `Int.toNat_of_nonneg (by omega)`. Simplify using `only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_w_eq (l : DomWeight a) : ∑ i, l.w i = ∑ i, ((l.natW i : ℕ) : ℤ) + (a : ℤ) * l.detShift := by
  have h : ∀ i, ((l.natW i : ℕ) : ℤ) = l.w i - l.detShift := by
    intro i
    have hpos : 0 < a := Fin.pos i
    have hle : l.w ⟨a - 1, by omega⟩ ≤ l.w i := l.anti (Fin.le_iff_val_le_val.2 (by simp; omega))
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hpos]
    exact Int.toNat_of_nonneg (by omega)
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/- English proof (translation)
Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, rfl⟩` from `hx`. Simplify using `only [evalAt_eq, ten, map_prod, MvPolynomial.eval_rename]`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `e : ((fun x : ι × Fin a × Fin a => y' x.1 x.2.1 x.2.2) ∘ Prod.mk τ) = z τ • ((fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) ∘ Prod.mk τ)`. Use function extensionality and compare the values at `x`. Simplify using `[hy τ]`. Rewrite using `[e, eval_smul_of_isHomogeneous (isHomogeneous_of_mem_delSq (lam τ) (hf τ))]`.

Consider the case `zero => simp [evalAt_eq]`. Consider the case `add p q _ _ hp hq => simp only [evalAt_eq, map_add] at *`. Rewrite using `[hp, hq]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul c p _ hp => simp only [evalAt_eq, MvPolynomial.smul_eval] at *`.

Rewrite using `[hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evalAt_scale_cSpan (lam : ι → DomWeight a) (z : ι → ℂ) (y y' : ι → Matrix (Fin a) (Fin a) ℂ)
    (hy : ∀ τ, y' τ = z τ • y τ) (P : PY ι a) (hP : P ∈ CSpan lam) :
    evalAt y' P = (∏ τ, z τ ^ (∑ i, (lam τ).natW i)) * evalAt y P := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    simp only [evalAt_eq, ten, map_prod, MvPolynomial.eval_rename]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have e : ((fun x : ι × Fin a × Fin a => y' x.1 x.2.1 x.2.2) ∘ Prod.mk τ) =
        z τ • ((fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) ∘ Prod.mk τ) := by
      funext x
      simp [hy τ]
    rw [e, eval_smul_of_isHomogeneous (isHomogeneous_of_mem_delSq (lam τ) (hf τ))]
  | zero => simp [evalAt_eq]
  | add p q _ _ hp hq => simp only [evalAt_eq, map_add] at *; rw [hp, hq]; ring
  | smul c p _ hp => simp only [evalAt_eq, MvPolynomial.smul_eval] at *; rw [hp]; ring

/- English proof (translation)
Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Establish `: y' = y` using `Subtype.ext (funext fun τ => Subsingleton.elim _ _)`. Simplify using `[this]`. Take `⟨P, hP, rfl⟩` from `hΦ`. Rewrite using `[fnOf_one_apply, fnOf_one_apply, evalAt_scale_cSpan lam z y.1 y'.1 hy P hP]`.

Establish `hz : ∀ τ, z τ ≠ 0`. Introduce `τ h0`. Establish `hne` using `(y'.2 τ).ne_zero`. Use `haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩`. Rewrite `hne` using `[hy τ, h0, zero_smul, Matrix.det_zero]`.

Conclude with `hne rfl`. Establish `per : ∀ (zz d : ℂ) (sh : ℤ) (deg : ℕ) (W : ℤ), zz ≠ 0 → W = deg + a * sh → (zz ^ a * d) ^ sh * zz ^ deg = zz ^ W * d ^ sh`. Introduce `zz d sh deg W hz hW`. Rewrite using `[mul_zpow, ← zpow_natCast zz a, ← _root_.zpow_mul, hW, zpow_add₀ hz, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key : (∏ τ, (y'.1 τ).det ^ shiftOf lam τ) * ∏ τ, z τ ^ (∑ i, (lam τ).natW i) = (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * ∏ τ, (y.1 τ).det ^ shiftOf lam τ`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[hy τ, Matrix.det_smul, Fintype.card_fin]`. Conclude with `per _ _ _ _ _ (hz τ) (by rw [sum_w_eq, Nat.cast_sum]; rfl)`.

Take the linear combination `(evalAt y.1 P) * key`.
-/
theorem valC_homog (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (Φ : Frames G → ℂ) (hΦ : Φ ∈ ValC G lam)
    (z : ι → ℂ) (y y' : Frames G) (hy : ∀ τ, y'.1 τ = z τ • y.1 τ) :
    Φ y' = (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * Φ y := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have : y' = y := Subtype.ext (funext fun τ => Subsingleton.elim _ _)
    simp [this]
  obtain ⟨P, hP, rfl⟩ := hΦ
  rw [fnOf_one_apply, fnOf_one_apply, evalAt_scale_cSpan lam z y.1 y'.1 hy P hP]
  have hz : ∀ τ, z τ ≠ 0 := by
    intro τ h0
    have hne := (y'.2 τ).ne_zero
    haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
    rw [hy τ, h0, zero_smul, Matrix.det_zero] at hne
    exact hne rfl
  have per : ∀ (zz d : ℂ) (sh : ℤ) (deg : ℕ) (W : ℤ), zz ≠ 0 → W = deg + a * sh →
      (zz ^ a * d) ^ sh * zz ^ deg = zz ^ W * d ^ sh := by
    intro zz d sh deg W hz hW
    rw [mul_zpow, ← zpow_natCast zz a, ← _root_.zpow_mul, hW, zpow_add₀ hz, zpow_natCast]
    ring
  have key : (∏ τ, (y'.1 τ).det ^ shiftOf lam τ) * ∏ τ, z τ ^ (∑ i, (lam τ).natW i) =
      (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * ∏ τ, (y.1 τ).det ^ shiftOf lam τ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hy τ, Matrix.det_smul, Fintype.card_fin]
    exact per _ _ _ _ _ (hz τ) (by rw [sum_w_eq, Nat.cast_sum]; rfl)
  linear_combination (evalAt y.1 P) * key

end GlobalTheory.KJInf.ValPol

/- English proof (translation)
Introduce `ι _ a G lam`. Use `⟨fun n s hns Φ => GlobalTheory.KJInf.ValPol.mem_valC_iff G lam n s hns Φ, GlobalTheory.KJInf.ValPol.finiteDimensional_valC G lam, fun Φ hΦ g Φ' hΦ' hg => GlobalTheory.KJInf.ValPol.valC_stable G lam Φ hΦ g Φ' hΦ' hg, fun Φ hΦ z y y' hy => GlobalTheory.KJInf.ValPol.valC_homog G lam …` and prove the remaining obligations.
-/
theorem GlobalTheory.KJInf.valC_poly : ∀ (ι : Type) [Fintype ι] (a : ℕ) (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a), (∀ (n : ι → ℕ) (s : ι → ℤ), (∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) → ∀ Φ : Frames G → ℂ, Φ ∈ ValC G lam ↔ ∃ F ∈ Vn lam n, ∀ y, Φ y = evalAt y.1 F * ∏ τ, (y.1 τ).det ^ (-s τ)) ∧ FiniteDimensional ℂ (ValC G lam) ∧ (∀ Φ ∈ ValC G lam, ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, ∀ Φ' : Frames G → ℂ, (∀ y y', IsTr g y y' → Φ' y = Φ y') → IsInv g → Φ' ∈ ValC G lam) ∧ ∀ Φ ∈ ValC G lam, ∀ (z : ι → ℂ) (y y' : Frames G), (∀ τ, y'.1 τ = z τ • y.1 τ) → Φ y' = (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * Φ y := by
  intro ι _ a G lam
  refine ⟨fun n s hns Φ => GlobalTheory.KJInf.ValPol.mem_valC_iff G lam n s hns Φ,
    GlobalTheory.KJInf.ValPol.finiteDimensional_valC G lam,
    fun Φ hΦ g Φ' hΦ' hg => GlobalTheory.KJInf.ValPol.valC_stable G lam Φ hΦ g Φ' hΦ' hg,
    fun Φ hΦ z y y' hy => GlobalTheory.KJInf.ValPol.valC_homog G lam Φ hΦ z y y' hy⟩

end
