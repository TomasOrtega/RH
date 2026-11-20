import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR.Compact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `g hg`. Establish `hgU : (fun x => g * x) '' U ∈ nhds g`. Establish `ho : IsOpen ((fun x => g * x) '' U)` using `(Homeomorph.mulLeft g).isOpenMap U hU`. Conclude with `ho.mem_nhds ⟨1, h1, mul_one g⟩`.

Use `Filter.mem_of_superset hgU ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Use `show ρ (g * u) v = v`. Rewrite using `[map_mul, Module.End.mul_apply, hfix u hu]`. Conclude with `hg`.
-/
theorem isOpen_fix {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    (hfix : ∀ u ∈ U, ρ u v = v) : IsOpen {g : G | ρ g v = v} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hgU : (fun x => g * x) '' U ∈ nhds g := by
    have ho : IsOpen ((fun x => g * x) '' U) := (Homeomorph.mulLeft g).isOpenMap U hU
    exact ho.mem_nhds ⟨1, h1, mul_one g⟩
  refine Filter.mem_of_superset hgU ?_
  rintro _ ⟨u, hu, rfl⟩
  show ρ (g * u) v = v
  rw [map_mul, Module.End.mul_apply, hfix u hu]
  exact hg

def rc (m : Levi k fun _ : Fin 2 => Fin d) : ℝ :=
  (nabs k (Matrix.GeneralLinearGroup.det (m 0)))⁻¹ * nabs k (Matrix.GeneralLinearGroup.det (m 1))

/- English proof (translation)
Unfold `rc`. Establish `h0` using `nabs_pos' k (Matrix.GeneralLinearGroup.det (m 0))`. Establish `h1` using `nabs_pos' k (Matrix.GeneralLinearGroup.det (m 1))`. Check the signs of the components of the expression.
-/
theorem rc_pos (m : Levi k fun _ : Fin 2 => Fin d) : 0 < rc m := by
  unfold rc
  have h0 := nabs_pos' k (Matrix.GeneralLinearGroup.det (m 0))
  have h1 := nabs_pos' k (Matrix.GeneralLinearGroup.det (m 1))
  positivity

/- English proof (translation)
Unfold `rc`. Simplify using `only [Pi.mul_apply, map_mul, nabs_mul', mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rc_mul (m m' : Levi k fun _ : Fin 2 => Fin d) : rc (m * m') = rc m * rc m' := by
  unfold rc
  simp only [Pi.mul_apply, map_mul, nabs_mul', mul_inv]
  ring

/- English proof (translation)
Establish `e : -(s : ℂ) = ((-s : ℝ) : ℂ)` using `by push_cast; ring`. Simplify using `only [chi, MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar_apply]`. Rewrite using `[e, val_absPow_ofReal, val_absPow_ofReal, ← Complex.ofReal_mul]`. Use `congr 1`. Unfold `rc`.

Establish `h0` using `(nabs_pos' k (Matrix.GeneralLinearGroup.det (m 0))).le`. Establish `h1` using `(nabs_pos' k (Matrix.GeneralLinearGroup.det (m 1))).le`. Rewrite using `[Real.mul_rpow (inv_nonneg.2 h0) h1, Real.inv_rpow h0, Real.rpow_neg h0]`.
-/
theorem chi_val (s : ℝ) (m : Levi k fun _ : Fin 2 => Fin d) :
    ((chi k d s m : ℂˣ) : ℂ) = ((rc m ^ s : ℝ) : ℂ) := by
  have e : -(s : ℂ) = ((-s : ℝ) : ℂ) := by push_cast; ring
  simp only [chi, MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
    detChar_apply]
  rw [e, val_absPow_ofReal, val_absPow_ofReal, ← Complex.ofReal_mul]
  congr 1
  unfold rc
  have h0 := (nabs_pos' k (Matrix.GeneralLinearGroup.det (m 0))).le
  have h1 := (nabs_pos' k (Matrix.GeneralLinearGroup.det (m 1))).le
  rw [Real.mul_rpow (inv_nonneg.2 h0) h1, Real.inv_rpow h0, Real.rpow_neg h0]

/- English proof (translation)
Establish `hK : ∀ a, leviProj k (blk2 d) q a ∈ KO k (Fin d)`. Introduce `a`. Rewrite using `[GlobalTheory.SplitFlip.mem_KO_iff]`. Take `⟨h1, h2⟩` from `(GlobalTheory.SplitFlip.mem_KO_iff _).1 hq`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[leviProj_apply]`. Conclude with `h1 _ _`. Establish `e : (leviProj k (blk2 d) q a)⁻¹ = leviProj k (blk2 d) q⁻¹ a` using `by rw [map_inv]; rfl`. Rewrite using `[e, leviProj_apply]`. Conclude with `h2 _ _`.

Unfold `rc`. Rewrite using `[GlobalTheory.LGrp.nabs_det_of_mem_KO (hK 0), GlobalTheory.LGrp.nabs_det_of_mem_KO (hK 1)]`. Simplify using the standard rewrite rules.
-/
theorem rc_of_KO (q : parab k (blk2 d)) (hq : (q : GL (Fin (d + d)) k) ∈ KO k (Fin (d + d))) :
    rc (leviProj k (blk2 d) q) = 1 := by
  have hK : ∀ a, leviProj k (blk2 d) q a ∈ KO k (Fin d) := by
    intro a
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hq
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [leviProj_apply]; exact h1 _ _
    · have e : (leviProj k (blk2 d) q a)⁻¹ = leviProj k (blk2 d) q⁻¹ a := by rw [map_inv]; rfl
      rw [e, leviProj_apply]
      exact h2 _ _
  unfold rc
  rw [GlobalTheory.LGrp.nabs_det_of_mem_KO (hK 0), GlobalTheory.LGrp.nabs_det_of_mem_KO (hK 1)]
  simp

/- English proof (translation)
Take `⟨u, g, w, hw, rfl⟩` from `GlobalTheory.SmGL.UnitInd.exists_iwasawa (blk2 d) x`. Conclude with `⟨⟨(u : GL (Fin (d + d)) k) * leviEmb k (blk2 d) g, mul_mem (unipRad_le_parab k (blk2 d) u.2) (leviEmb_mem_parab k (blk2 d) g)⟩, w, hw, rfl⟩`.
-/
theorem exists_pw (x : GL (Fin (d + d)) k) :
    ∃ p : parab k (blk2 d), ∃ w ∈ KO k (Fin (d + d)), x = (p : GL (Fin (d + d)) k) * w := by
  obtain ⟨u, g, w, hw, rfl⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa (blk2 d) x
  exact ⟨⟨(u : GL (Fin (d + d)) k) * leviEmb k (blk2 d) g,
    mul_mem (unipRad_le_parab k (blk2 d) u.2) (leviEmb_mem_parab k (blk2 d) g)⟩, w, hw, rfl⟩

def hh (x : GL (Fin (d + d)) k) : ℝ := rc (leviProj k (blk2 d) (Classical.choose (exists_pw x)))

/- English proof (translation)
Take `⟨w', hw', e⟩` from `Classical.choose_spec (exists_pw ((p : GL (Fin (d + d)) k) * w))`. Use `set p' := Classical.choose (exists_pw ((p : GL (Fin (d + d)) k) * w))`. Establish `hq : ((p'⁻¹ * p : parab k (blk2 d)) : GL (Fin (d + d)) k) ∈ KO k (Fin (d + d))`. Establish `: ((p'⁻¹ * p : parab k (blk2 d)) : GL (Fin (d + d)) k) = w' * w⁻¹`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]`.

Use `group`. Rewrite using `[this]`. Conclude with `mul_mem hw' (inv_mem hw)`. Establish `h1 : p = p' * (p'⁻¹ * p)` using `by group`. Use `show rc (leviProj k (blk2 d) p') = _`.

Use `conv_rhs => rw [h1, map_mul, rc_mul, rc_of_KO _ hq, mul_one]`.
-/
theorem hh_spec (p : parab k (blk2 d)) (w : GL (Fin (d + d)) k) (hw : w ∈ KO k (Fin (d + d))) :
    hh ((p : GL (Fin (d + d)) k) * w) = rc (leviProj k (blk2 d) p) := by
  obtain ⟨w', hw', e⟩ := Classical.choose_spec (exists_pw ((p : GL (Fin (d + d)) k) * w))
  set p' := Classical.choose (exists_pw ((p : GL (Fin (d + d)) k) * w))
  have hq : ((p'⁻¹ * p : parab k (blk2 d)) : GL (Fin (d + d)) k) ∈ KO k (Fin (d + d)) := by
    have : ((p'⁻¹ * p : parab k (blk2 d)) : GL (Fin (d + d)) k) = w' * w⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
      group
    rw [this]
    exact mul_mem hw' (inv_mem hw)
  have h1 : p = p' * (p'⁻¹ * p) := by group
  show rc (leviProj k (blk2 d) p') = _
  conv_rhs => rw [h1, map_mul, rc_mul, rc_of_KO _ hq, mul_one]

/- English proof (translation)
The claim follows from `rc_pos _`.
-/
theorem hh_pos (x : GL (Fin (d + d)) k) : 0 < hh x := rc_pos _

/- English proof (translation)
Take `⟨p', w, hw, rfl⟩` from `exists_pw (d := d) x`. Rewrite using `[← mul_assoc, ← Subgroup.coe_mul, hh_spec _ _ hw, hh_spec _ _ hw, map_mul, rc_mul]`.
-/
theorem hh_mul_left (p : parab k (blk2 d)) (x : GL (Fin (d + d)) k) :
    hh ((p : GL (Fin (d + d)) k) * x) = rc (leviProj k (blk2 d) p) * hh x := by
  obtain ⟨p', w, hw, rfl⟩ := exists_pw (d := d) x
  rw [← mul_assoc, ← Subgroup.coe_mul, hh_spec _ _ hw, hh_spec _ _ hw, map_mul, rc_mul]

/- English proof (translation)
Take `⟨p', w', hw', rfl⟩` from `exists_pw (d := d) x`. Rewrite using `[mul_assoc, hh_spec _ _ (mul_mem hw' hw), hh_spec _ _ hw']`.
-/
theorem hh_mul_right (x w : GL (Fin (d + d)) k) (hw : w ∈ KO k (Fin (d + d))) : hh (x * w) = hh x := by
  obtain ⟨p', w', hw', rfl⟩ := exists_pw (d := d) x
  rw [mul_assoc, hh_spec _ _ (mul_mem hw' hw), hh_spec _ _ hw']

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def mulFun (a : ℝ) (f : GL (Fin (d + d)) k → W) : GL (Fin (d + d)) k → W := fun x => ((hh x ^ a : ℝ) : ℂ) • f x

/- English proof (translation)
Introduce `p g`. Use `show ((hh ((p : GL (Fin (d + d)) k) * g) ^ a : ℝ) : ℂ) • f.1.1 ((p : GL (Fin (d + d)) k) * g) = (deltaHalf k (fun _ : Fin 2 => Fin d) (leviProj k (blk2 d) p) : ℂ) • τ₂ (leviProj k (blk2 d) p) (((hh g ^ a : ℝ) : ℂ) • f.1.1 g)`. Establish `hf : f.1.1 ((p : GL (Fin (d + d)) k) * g) = (deltaHalf k (fun _ : Fin 2 => Fin d) (leviProj k (blk2 d) p) : ℂ) • τ₁ (leviProj k (blk2 d) p) (f.1.1 g)` using `f.1.2 p g`. Rewrite using `[hf, hrel, hh_mul_left, Real.mul_rpow (rc_pos _).le (hh_pos _).le]`. Simplify using `only [map_smul, smul_smul, Complex.ofReal_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mulFun_mem (a : ℝ) (τ₁ τ₂ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)
    (hrel : ∀ m v, τ₂ m v = ((rc m ^ a : ℝ) : ℂ) • τ₁ m v) (f : IndSp (blk2 d) τ₁) :
    mulFun a f.1.1 ∈ indSpace (parab k (blk2 d)) ((twist τ₂ (deltaHalf k fun _ : Fin 2 => Fin d)).comp
      (leviProj k (blk2 d))) := by
  intro p g
  show ((hh ((p : GL (Fin (d + d)) k) * g) ^ a : ℝ) : ℂ) • f.1.1 ((p : GL (Fin (d + d)) k) * g) =
    (deltaHalf k (fun _ : Fin 2 => Fin d) (leviProj k (blk2 d) p) : ℂ) •
      τ₂ (leviProj k (blk2 d) p) (((hh g ^ a : ℝ) : ℂ) • f.1.1 g)
  have hf : f.1.1 ((p : GL (Fin (d + d)) k) * g) =
      (deltaHalf k (fun _ : Fin 2 => Fin d) (leviProj k (blk2 d) p) : ℂ) • τ₁ (leviProj k (blk2 d) p) (f.1.1 g) :=
    f.1.2 p g
  rw [hf, hrel, hh_mul_left, Real.mul_rpow (rc_pos _).le (hh_pos _).le]
  simp only [map_smul, smul_smul, Complex.ofReal_mul]
  congr 1
  ring

/- English proof (translation)
Establish `hf2 : IsOpen {g : GL (Fin (d + d)) k | ind (parab k (blk2 d)) ((twist τ₁ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d))) g f.1 = f.1}` using `f.2`. Use `isOpen_fix (ind (parab k (blk2 d)) ((twist τ₂ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d)))) _ _ (hf2.inter GlobalTheory.SplitFlip.isOpen_KO) ⟨by simp, one_mem _⟩ ?_` and prove the remaining obligations. Introduce and unpack `u ⟨hu1, hu2⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Use `show ((hh (x * u) ^ a : ℝ) : ℂ) • f.1.1 (x * u) = ((hh x ^ a : ℝ) : ℂ) • f.1.1 x`. Establish `hf : f.1.1 (x * u) = f.1.1 x` using `congrFun (congrArg Subtype.val hu1) x`. Rewrite using `[hh_mul_right x u hu2, hf]`.
-/
theorem mulFun_smooth (a : ℝ) (τ₁ τ₂ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)
    (hrel : ∀ m v, τ₂ m v = ((rc m ^ a : ℝ) : ℂ) • τ₁ m v) (f : IndSp (blk2 d) τ₁) :
    (⟨mulFun a f.1.1, mulFun_mem a τ₁ τ₂ hrel f⟩ : indSpace _ _) ∈ smoothPart (ind (parab k (blk2 d))
      ((twist τ₂ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d)))) := by
  have hf2 : IsOpen {g : GL (Fin (d + d)) k | ind (parab k (blk2 d))
      ((twist τ₁ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d))) g f.1 = f.1} := f.2
  refine isOpen_fix (ind (parab k (blk2 d)) ((twist τ₂ (deltaHalf k fun _ : Fin 2 => Fin d)).comp
      (leviProj k (blk2 d)))) _ _ (hf2.inter GlobalTheory.SplitFlip.isOpen_KO) ⟨by simp, one_mem _⟩ ?_
  rintro u ⟨hu1, hu2⟩
  apply Subtype.ext
  funext x
  show ((hh (x * u) ^ a : ℝ) : ℂ) • f.1.1 (x * u) = ((hh x ^ a : ℝ) : ℂ) • f.1.1 x
  have hf : f.1.1 (x * u) = f.1.1 x := congrFun (congrArg Subtype.val hu1) x
  rw [hh_mul_right x u hu2, hf]

def mulMap (a : ℝ) (τ₁ τ₂ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)
    (hrel : ∀ m v, τ₂ m v = ((rc m ^ a : ℝ) : ℂ) • τ₁ m v) : IndSp (blk2 d) τ₁ →ₗ[ℂ] IndSp (blk2 d) τ₂ where
  toFun f := ⟨⟨mulFun a f.1.1, mulFun_mem a τ₁ τ₂ hrel f⟩, mulFun_smooth a τ₁ τ₂ hrel f⟩
  map_add' f g := by
    apply Subtype.ext; apply Subtype.ext; funext x
    show ((hh x ^ a : ℝ) : ℂ) • (f.1.1 x + g.1.1 x) = ((hh x ^ a : ℝ) : ℂ) • f.1.1 x + ((hh x ^ a : ℝ) : ℂ) • g.1.1 x
    rw [smul_add]
  map_smul' c f := by
    apply Subtype.ext; apply Subtype.ext; funext x
    show ((hh x ^ a : ℝ) : ℂ) • (c • f.1.1 x) = c • (((hh x ^ a : ℝ) : ℂ) • f.1.1 x)
    rw [smul_comm]

/- English proof (translation)
Introduce `m v`. Rewrite using `[hrel, smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (rc_pos m), neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_smul]`.
-/
theorem rel_symm (a : ℝ) (τ₁ τ₂ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)
    (hrel : ∀ m v, τ₂ m v = ((rc m ^ a : ℝ) : ℂ) • τ₁ m v) :
    ∀ m v, τ₁ m v = ((rc m ^ (-a) : ℝ) : ℂ) • τ₂ m v := by
  intro m v
  rw [hrel, smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (rc_pos m), neg_add_cancel, Real.rpow_zero,
    Complex.ofReal_one, one_smul]

def mulEquiv (a : ℝ) (τ₁ τ₂ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)
    (hrel : ∀ m v, τ₂ m v = ((rc m ^ a : ℝ) : ℂ) • τ₁ m v) : IndSp (blk2 d) τ₁ ≃ₗ[ℂ] IndSp (blk2 d) τ₂ :=
  { mulMap a τ₁ τ₂ hrel with
    invFun := mulMap (-a) τ₂ τ₁ (rel_symm a τ₁ τ₂ hrel)
    left_inv := fun f => by
      apply Subtype.ext; apply Subtype.ext; funext x
      show ((hh x ^ (-a) : ℝ) : ℂ) • ((hh x ^ a : ℝ) : ℂ) • f.1.1 x = f.1.1 x
      rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (hh_pos x), neg_add_cancel, Real.rpow_zero,
        Complex.ofReal_one, one_smul]
    right_inv := fun f => by
      apply Subtype.ext; apply Subtype.ext; funext x
      show ((hh x ^ a : ℝ) : ℂ) • ((hh x ^ (-a) : ℝ) : ℂ) • f.1.1 x = f.1.1 x
      rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (hh_pos x), add_neg_cancel, Real.rpow_zero,
        Complex.ofReal_one, one_smul] }

variable (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)

/- English proof (translation)
Introduce `m v`. Use `show ((chi k d s m : ℂˣ) : ℂ) • τ m v = _`. Rewrite using `[chi_val]`.
-/
theorem relChi (s : ℝ) : ∀ m v, twist τ (chi k d s) m v = ((rc m ^ s : ℝ) : ℂ) • τ m v := by
  intro m v
  show ((chi k d s m : ℂˣ) : ℂ) • τ m v = _
  rw [chi_val]

def E (s : ℝ) : IndSp (blk2 d) τ ≃ₗ[ℂ] IndSp (blk2 d) (twist τ (chi k d s)) :=
  mulEquiv s τ (twist τ (chi k d s)) (relChi τ s)

def F (s : ℝ) : Representation ℂ (GL (Fin (d + d)) k) (IndSp (blk2 d) τ) where
  toFun g := (E τ s).symm.toLinearMap ∘ₗ parInd (blk2 d) (twist τ (chi k d s)) g ∘ₗ (E τ s).toLinearMap
  map_one' := by
    ext f : 1
    simp
  map_mul' g g' := by
    ext f : 1
    simp [map_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem F_apply (s : ℝ) (g : GL (Fin (d + d)) k) (f : IndSp (blk2 d) τ) (y : GL (Fin (d + d)) k) :
    (F τ s g f).1.1 y = ((hh y ^ (-s) : ℝ) : ℂ) • ((hh (y * g) ^ s : ℝ) : ℂ) • f.1.1 (y * g) := rfl

def cc (g y : GL (Fin (d + d)) k) : ℝ := hh (y * g) / hh y

/- English proof (translation)
Unfold `cc`. Rewrite using `[mul_assoc, hh_mul_left, hh_mul_left, mul_div_mul_left _ _ (rc_pos _).ne']`.
-/
theorem cc_left (g : GL (Fin (d + d)) k) (p : parab k (blk2 d)) (y : GL (Fin (d + d)) k) :
    cc g ((p : GL (Fin (d + d)) k) * y) = cc g y := by
  unfold cc
  rw [mul_assoc, hh_mul_left, hh_mul_left, mul_div_mul_left _ _ (rc_pos _).ne']

def K1 (g : GL (Fin (d + d)) k) : Set (GL (Fin (d + d)) k) :=
  (KO k (Fin (d + d)) : Set _) ∩ (fun w => g⁻¹ * w * g) ⁻¹' (KO k (Fin (d + d)) : Set _)

/- English proof (translation)
The claim follows from `GlobalTheory.SplitFlip.isOpen_KO.inter (GlobalTheory.SplitFlip.isOpen_KO.preimage (by fun_prop))`.
-/
theorem isOpen_compact_open_subgroup (g : GL (Fin (d + d)) k) : IsOpen (K1 (k := k) g) :=
  GlobalTheory.SplitFlip.isOpen_KO.inter (GlobalTheory.SplitFlip.isOpen_KO.preimage (by fun_prop))

/- English proof (translation)
Unfold `cc`. Establish `e : y * w * g = y * g * (g⁻¹ * w * g)` using `by group`. Rewrite using `[e, hh_mul_right _ _ hw.2, hh_mul_right _ _ hw.1]`.
-/
theorem cc_right (g y w : GL (Fin (d + d)) k) (hw : w ∈ K1 g) : cc g (y * w) = cc g y := by
  unfold cc
  have e : y * w * g = y * g * (g⁻¹ * w * g) := by group
  rw [e, hh_mul_right _ _ hw.2, hh_mul_right _ _ hw.1]

/- English proof (translation)
Establish `hc : CompactSpace (KO k (Fin (d + d)))` using `isCompact_iff_compactSpace.mp GlobalTheory.SplitFlip.isCompact_KO`. Establish `hl : IsLocallyConstant fun w : KO k (Fin (d + d)) => cc g (w : GL (Fin (d + d)) k)`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `w`. Establish `ho : IsOpen ((fun y : KO k (Fin (d + d)) => (w : GL (Fin (d + d)) k)⁻¹ * y) ⁻¹' K1 g)` using `(isOpen_compact_open_subgroup g).preimage (by fun_prop)`.

Use `Filter.mem_of_superset (ho.mem_nhds ?_) fun y hy => ?_` and prove the remaining obligations. Use `show (w : GL (Fin (d + d)) k)⁻¹ * w ∈ K1 g`. Rewrite using `[inv_mul_cancel]`. Conclude with `⟨one_mem _, by simp⟩`. Establish `e : (y : GL (Fin (d + d)) k) = w * ((w : GL (Fin (d + d)) k)⁻¹ * y)` using `by group show cc g (y : GL (Fin (d + d)) k) = cc g w`.

Rewrite using `[e, cc_right _ _ _ hy]`. Use `hl.range_finite.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨p, w, hw, rfl⟩` from `exists_pw (d := d) y`. Conclude with `⟨⟨w, hw⟩, (cc_left g p w).symm⟩`.
-/
theorem cc_finite (g : GL (Fin (d + d)) k) : (Set.range (cc (k := k) g)).Finite := by
  have hc : CompactSpace (KO k (Fin (d + d))) := isCompact_iff_compactSpace.mp GlobalTheory.SplitFlip.isCompact_KO
  have hl : IsLocallyConstant fun w : KO k (Fin (d + d)) => cc g (w : GL (Fin (d + d)) k) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    have ho : IsOpen ((fun y : KO k (Fin (d + d)) => (w : GL (Fin (d + d)) k)⁻¹ * y) ⁻¹' K1 g) :=
      (isOpen_compact_open_subgroup g).preimage (by fun_prop)
    refine Filter.mem_of_superset (ho.mem_nhds ?_) fun y hy => ?_
    · show (w : GL (Fin (d + d)) k)⁻¹ * w ∈ K1 g
      rw [inv_mul_cancel]
      exact ⟨one_mem _, by simp⟩
    · have e : (y : GL (Fin (d + d)) k) = w * ((w : GL (Fin (d + d)) k)⁻¹ * y) := by group
      show cc g (y : GL (Fin (d + d)) k) = cc g w
      rw [e, cc_right _ _ _ hy]
  refine hl.range_finite.subset ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨p, w, hw, rfl⟩ := exists_pw (d := d) y
  exact ⟨⟨w, hw⟩, (cc_left g p w).symm⟩

/- English proof (translation)
Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]`.
-/
theorem ind_val_sum {σ : Representation ℂ (parab k (blk2 d)) W} {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (u : ι → smoothPart (ind (parab k (blk2 d)) σ)) (y : GL (Fin (d + d)) k) :
    (∑ i ∈ s, c i • u i).1.1 y = ∑ i ∈ s, c i • (u i).1.1 y := by
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]

def piece (g : GL (Fin (d + d)) k) (v : ℝ) (f : IndSp (blk2 d) τ) : IndSp (blk2 d) τ :=
  ⟨⟨fun y => if cc g y = v then f.1.1 (y * g) else 0, by
      intro p y
      show (if cc g ((p : GL (Fin (d + d)) k) * y) = v then f.1.1 ((p : GL (Fin (d + d)) k) * y * g) else 0) =
        ((twist τ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d))) p
          (if cc g y = v then f.1.1 (y * g) else 0)
      rw [cc_left]
      split_ifs
      · rw [mul_assoc]; exact f.1.2 p (y * g)
      · rw [map_zero]⟩, by
      have hf2 : IsOpen {x : GL (Fin (d + d)) k | ind (parab k (blk2 d))
          ((twist τ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d))) x f.1 = f.1} := f.2
      refine isOpen_fix (ind (parab k (blk2 d)) ((twist τ (deltaHalf k fun _ : Fin 2 => Fin d)).comp
          (leviProj k (blk2 d)))) _ (((fun w => g⁻¹ * w * g) ⁻¹' {x : GL (Fin (d + d)) k | ind (parab k (blk2 d))
          ((twist τ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d))) x f.1 = f.1}) ∩ K1 g)
        ((hf2.preimage (by fun_prop)).inter (isOpen_compact_open_subgroup g)) ⟨?_, ?_⟩ ?_
      · show ind _ _ (g⁻¹ * 1 * g) f.1 = f.1
        rw [mul_one, inv_mul_cancel, map_one]; rfl
      · show (1 : GL (Fin (d + d)) k) ∈ K1 g
        exact ⟨one_mem _, by simp⟩
      rintro w ⟨hu1, hu2⟩
      apply Subtype.ext
      funext y
      show (if cc g (y * w) = v then f.1.1 (y * w * g) else 0) = (if cc g y = v then f.1.1 (y * g) else 0)
      have hf : f.1.1 (y * g * (g⁻¹ * w * g)) = f.1.1 (y * g) :=
        congrFun (congrArg Subtype.val (show ind _ _ (g⁻¹ * w * g) f.1 = f.1 from hu1)) (y * g)
      have e : y * w * g = y * g * (g⁻¹ * w * g) := by group
      rw [cc_right _ _ _ hu2, e, hf]⟩

/- English proof (translation)
Use `set S := (cc_finite (k := k) g).toFinset`. Set `v : Fin S.card → ℝ` to `fun i => (S.equivFin.symm i : ℝ)`. Establish `hv : Function.Injective v` using `fun i j h => S.equivFin.symm.injective (Subtype.ext h)`. Use `⟨S.card, fun i => Real.log (v i), fun i => piece τ g (v i) f, fun s => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `y`. Rewrite using `[ind_val_sum, F_apply]`. Establish `hy : cc g y ∈ S` using `(Set.Finite.mem_toFinset _).2 ⟨y, rfl⟩`. Take `⟨i0, hi0⟩ : ∃ i0, v i0 = cc g y` from `⟨S.equivFin ⟨cc g y, hy⟩, by simp [v]⟩`.

Rewrite using `[Fintype.sum_eq_single i0]`. Use `show _ = ((Real.exp (Real.log (v i0) * s) : ℝ) : ℂ) • (if cc g y = v i0 then f.1.1 (y * g) else 0)`. Rewrite using `[if_pos hi0.symm, hi0, smul_smul, ← Complex.ofReal_mul]`. Use `congr 2`. Establish `hpos : 0 < cc g y` using `div_pos (hh_pos _) (hh_pos _)`.

Rewrite using `[← Real.rpow_def_of_pos hpos]`. Unfold `cc`. Rewrite using `[Real.div_rpow (hh_pos _).le (hh_pos _).le, div_eq_inv_mul, Real.rpow_neg (hh_pos _).le]`. Introduce `i hi show ((Real.exp (Real.log (v i) * s) : ℝ) : ℂ) • (if cc g y = v i then f.1.1 (y * g) else 0) = 0`. Rewrite using `[if_neg (fun h => hi (hv (h.symm.trans hi0.symm))), smul_zero]`.
-/
theorem expo (g : GL (Fin (d + d)) k) (f : IndSp (blk2 d) τ) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (u : Fin m → IndSp (blk2 d) τ),
      ∀ s, F τ s g f = ∑ i, ((Real.exp (r i * s) : ℝ) : ℂ) • u i := by
  classical
  set S := (cc_finite (k := k) g).toFinset
  let v : Fin S.card → ℝ := fun i => (S.equivFin.symm i : ℝ)
  have hv : Function.Injective v := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  refine ⟨S.card, fun i => Real.log (v i), fun i => piece τ g (v i) f, fun s => ?_⟩
  apply Subtype.ext; apply Subtype.ext; funext y
  rw [ind_val_sum, F_apply]
  have hy : cc g y ∈ S := (Set.Finite.mem_toFinset _).2 ⟨y, rfl⟩
  obtain ⟨i0, hi0⟩ : ∃ i0, v i0 = cc g y := ⟨S.equivFin ⟨cc g y, hy⟩, by simp [v]⟩
  rw [Fintype.sum_eq_single i0]
  · show _ = ((Real.exp (Real.log (v i0) * s) : ℝ) : ℂ) • (if cc g y = v i0 then f.1.1 (y * g) else 0)
    rw [if_pos hi0.symm, hi0, smul_smul, ← Complex.ofReal_mul]
    congr 2
    have hpos : 0 < cc g y := div_pos (hh_pos _) (hh_pos _)
    rw [← Real.rpow_def_of_pos hpos]
    unfold cc
    rw [Real.div_rpow (hh_pos _).le (hh_pos _).le, div_eq_inv_mul, Real.rpow_neg (hh_pos _).le]
  · intro i hi
    show ((Real.exp (Real.log (v i) * s) : ℝ) : ℂ) • (if cc g y = v i then f.1.1 (y * g) else 0) = 0
    rw [if_neg (fun h => hi (hv (h.symm.trans hi0.symm))), smul_zero]

end PositivityTheory.RgGu.NR.Compact

namespace PositivityTheory.RgGu.NR

open PositivityTheory.RgGu.NR.Compact in
/- English proof (translation)
Introduce `d W _ _ τ`. Use `⟨KO k (Fin (d + d)), F τ, GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `s x hx`. Use extensionality with `f : 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `y`. Rewrite using `[F_apply, F_apply, hh_mul_right y x hx, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.rpow_add (hh_pos y), ← Real.rpow_add (hh_pos y)]`. Simplify using the standard rewrite rules. Conclude with `fun g f => expo τ g f`.

Introduce `s`. Conclude with `⟨Representation.Equiv.mk (E τ s) fun g => by`. Use extensionality with `f : 1`. Simplify using `[F]⟩`.
-/
theorem compact (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Compact k := by
  intro d W _ _ τ
  refine ⟨KO k (Fin (d + d)), F τ, GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO, ⟨?_, ?_⟩, ?_⟩
  · intro s x hx
    ext f : 1
    apply Subtype.ext; apply Subtype.ext; funext y
    rw [F_apply, F_apply, hh_mul_right y x hx, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Real.rpow_add (hh_pos y), ← Real.rpow_add (hh_pos y)]
    simp
  · exact fun g f => expo τ g f
  · intro s
    exact ⟨Representation.Equiv.mk (E τ s) fun g => by
      ext f : 1
      simp [F]⟩

end PositivityTheory.RgGu.NR
