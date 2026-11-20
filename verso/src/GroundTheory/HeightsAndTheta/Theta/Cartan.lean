import Mathlib
import GroundTheory.AutomorphicForms.RealGroupsPolar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact

namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {p q : ℕ}

local notation "𝔐" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
local notation "J" => indefJ p q

/- English proof (translation)
Establish `h1 : (J * gᴴ * J) * g = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : g * (J * gᴴ * J) = 1` using `mul_eq_one_comm.1 h1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]`.

Use `_ = J := by rw [h2, Matrix.one_mul]`.
-/
theorem mul_indefJ_mul_conjTranspose {g : 𝔐} (hg : gᴴ * J * g = J) : g * J * gᴴ = J := by
  have h1 : (J * gᴴ * J) * g = 1 := by
    calc (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, indefJ_mul_self]
  have h2 : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.1 h1
  calc g * J * gᴴ = g * (J * gᴴ * J) * J := by
        simp only [Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
    _ = J := by rw [h2, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[conjTranspose_conjTranspose]`. Conclude with `mul_indefJ_mul_conjTranspose hg`.
-/
theorem conjTranspose_preservesIndefJ {g : 𝔐} (hg : gᴴ * J * g = J) : gᴴᴴ * J * gᴴ = J := by
  rw [conjTranspose_conjTranspose]
  exact mul_indefJ_mul_conjTranspose hg

/- English proof (translation)
Use `set S := CFC.sqrt P with hSdef`. Establish `hSpd : S.PosDef`. Rewrite `hP`, the goal using `[← isStrictlyPositive_iff_posDef]`. Conclude with `IsStrictlyPositive.sqrt _ hP`. Establish `hSh : Sᴴ = S` using `hSpd.isHermitian`.

Establish `hPh : Pᴴ = P` using `hP.isHermitian`. Establish `hSS : S * S = P` using `CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg`. Establish `hJh : Jᴴ = J` using `indefJ_conjTranspose p q`. Establish `hJJ : J * J = 1` using `indefJ_mul_self p q`. Establish `hPJ' : P * J * P = J` using `by rwa [hPh] at hPJ`.

Establish `hJPJ : J * P * J = P⁻¹`. Use `(Matrix.inv_eq_left_inv ?_).symm` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : CFC.sqrt (J * P * J) = J * S * J`. Use `CFC.sqrt_unique ?_ ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `hSpd.posSemidef.conjTranspose_mul_mul_same J` as an intermediate fact. Rewrite `this` using `[hJh]`. Conclude with `this.nonneg`. Establish `h2 : CFC.sqrt P⁻¹ = S⁻¹`.

Use `CFC.sqrt_unique ?_ hSpd.inv.posSemidef.nonneg` and prove the remaining obligations. Rewrite using `[← Matrix.mul_inv_rev, hSS]`. Establish `h3 : J * S * J = S⁻¹` using `by rw [← h1, hJPJ, h2]`. Establish `hSu : IsUnit S.det` using `(Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit`. Rewrite using `[hSh]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, hJJ, Matrix.mul_one]`. Use `_ = J := by rw [h3, Matrix.mul_nonsing_inv _ hSu, Matrix.one_mul]`.
-/
theorem sqrt_preservesIndefJ {P : 𝔐} (hP : P.PosDef) (hPJ : Pᴴ * J * P = J) :
    (CFC.sqrt P)ᴴ * J * CFC.sqrt P = J := by
  set S := CFC.sqrt P with hSdef
  have hSpd : S.PosDef := by
    rw [← isStrictlyPositive_iff_posDef] at hP ⊢
    exact IsStrictlyPositive.sqrt _ hP
  have hSh : Sᴴ = S := hSpd.isHermitian
  have hPh : Pᴴ = P := hP.isHermitian
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg
  have hJh : Jᴴ = J := indefJ_conjTranspose p q
  have hJJ : J * J = 1 := indefJ_mul_self p q
  have hPJ' : P * J * P = J := by rwa [hPh] at hPJ
  have hJPJ : J * P * J = P⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    calc J * P * J * P = J * (P * J * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPJ', hJJ]
  have h1 : CFC.sqrt (J * P * J) = J * S * J := by
    refine CFC.sqrt_unique ?_ ?_
    · calc J * S * J * (J * S * J) = J * S * (J * J) * S * J := by simp only [Matrix.mul_assoc]
        _ = J * P * J := by rw [hJJ, Matrix.mul_one, Matrix.mul_assoc J S S, hSS]
    · have := hSpd.posSemidef.conjTranspose_mul_mul_same J
      rw [hJh] at this
      exact this.nonneg
  have h2 : CFC.sqrt P⁻¹ = S⁻¹ := by
    refine CFC.sqrt_unique ?_ hSpd.inv.posSemidef.nonneg
    rw [← Matrix.mul_inv_rev, hSS]
  have h3 : J * S * J = S⁻¹ := by rw [← h1, hJPJ, h2]
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit
  rw [hSh]
  calc S * J * S = S * (J * S * J) * J := by
        simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = J := by rw [h3, Matrix.mul_nonsing_inv _ hSu, Matrix.one_mul]

section Polar

local notation "G" => indefiniteUnitaryGroup p q

/- English proof (translation)
Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_preservesIndefJ {a b : 𝔐} (ha : aᴴ * J * a = J) (hb : bᴴ * J * b = J) :
    (a * b)ᴴ * J * (a * b) = J := by
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * J * (a * b) = bᴴ * (aᴴ * J * a) * b := by simp only [Matrix.mul_assoc]
    _ = J := by rw [ha, hb]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_preservesIndefJ {a : 𝔐} (hu : IsUnit a.det) (ha : aᴴ * J * a = J) :
    a⁻¹ᴴ * J * a⁻¹ = J := by
  calc a⁻¹ᴴ * J * a⁻¹ = a⁻¹ᴴ * (aᴴ * J * a) * a⁻¹ := by rw [ha]
    _ = (a * a⁻¹)ᴴ * J * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = J := by rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def upqOfMatrix (m : 𝔐) (hm : mᴴ * J * m = J) : G :=
  ⟨⟨m, J * mᴴ * J, by
      calc m * (J * mᴴ * J) = m * J * mᴴ * J := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [mul_indefJ_mul_conjTranspose hm, indefJ_mul_self],
    by
      calc J * mᴴ * J * m = J * (mᴴ * J * m) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hm, indefJ_mul_self]⟩, hm⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_upqOfMatrix (m : 𝔐) (hm : mᴴ * J * m = J) :
    ((upqOfMatrix m hm : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) = m := rfl

/- English proof (translation)
Establish `h : Continuous fun x => ((upqOfMatrix (f x) (hfJ x) : G) : GL (Fin p ⊕ Fin q) ℂ)` using `Units.continuous_iff.2 ⟨hf, (continuous_const.mul hf.matrix_conjTranspose).mul continuous_const⟩`. Conclude with `h.subtype_mk _`.
-/
theorem continuous_upqOfMatrix {X : Type*} [TopologicalSpace X] {f : X → 𝔐}
    (hf : Continuous f) (hfJ : ∀ x, (f x)ᴴ * J * f x = J) :
    Continuous fun x => upqOfMatrix (f x) (hfJ x) := by
  have h : Continuous fun x => ((upqOfMatrix (f x) (hfJ x) : G) : GL (Fin p ⊕ Fin q) ℂ) :=
    Units.continuous_iff.2
      ⟨hf, (continuous_const.mul hf.matrix_conjTranspose).mul continuous_const⟩
  exact h.subtype_mk _

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_coe_indefiniteUnitary :
    Continuous fun g : G => ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Use `set m := ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)`. Establish `hg : mᴴ * J * m = J` using `g.2`. Establish `hg' : m * J * mᴴ = J` using `mul_indefJ_mul_conjTranspose hg`. Use `sqrt_preservesIndefJ (posDef_conjTranspose_mul_self_GL _) ?_` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem polarPos_preservesIndefJ (g : G) :
    (polarPos (g : GL (Fin p ⊕ Fin q) ℂ))ᴴ * J * polarPos (g : GL (Fin p ⊕ Fin q) ℂ) = J := by
  set m := ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)
  have hg : mᴴ * J * m = J := g.2
  have hg' : m * J * mᴴ = J := mul_indefJ_mul_conjTranspose hg
  refine sqrt_preservesIndefJ (posDef_conjTranspose_mul_self_GL _) ?_
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc mᴴ * m * J * (mᴴ * m) = mᴴ * (m * J * mᴴ) * m := by simp only [Matrix.mul_assoc]
    _ = J := by rw [hg', hg]

/- English proof (translation)
The claim follows from `mul_preservesIndefJ g.2 (inv_preservesIndefJ (isUnit_det_of_posDef (polarPos_posDef _)) (polarPos_preservesIndefJ g))`.
-/
theorem polarUnitary_preservesIndefJ (g : G) :
    (polarUnitary (g : GL (Fin p ⊕ Fin q) ℂ))ᴴ * J * polarUnitary (g : GL (Fin p ⊕ Fin q) ℂ) =
      J :=
  mul_preservesIndefJ g.2 (inv_preservesIndefJ (isUnit_det_of_posDef (polarPos_posDef _))
    (polarPos_preservesIndefJ g))

def cartanPos (p q : ℕ) : Set (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
  {s | s.PosDef ∧ sᴴ * indefJ p q * s = indefJ p q}

def cartanMul (ks : maxCompact G × cartanPos p q) : G :=
  (ks.1 : G) * upqOfMatrix ks.2.1 ks.2.2.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_cartanMul (ks : maxCompact G × cartanPos p q) :
    ((cartanMul ks : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) =
      (((ks.1 : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) * ks.2.1 := rfl

noncomputable def cartanSplit (g : G) : maxCompact G × cartanPos p q :=
  (⟨upqOfMatrix (polarUnitary (g : GL (Fin p ⊕ Fin q) ℂ)) (polarUnitary_preservesIndefJ g),
      polarUnitary_mem (g : GL (Fin p ⊕ Fin q) ℂ)⟩,
    ⟨polarPos (g : GL (Fin p ⊕ Fin q) ℂ), polarPos_posDef _, polarPos_preservesIndefJ g⟩)

noncomputable def cartanHomeomorph : maxCompact G × cartanPos p q ≃ₜ G where
  toFun := cartanMul
  invFun := cartanSplit
  left_inv ks := by
    obtain ⟨⟨k, hk⟩, ⟨s, hs, hsJ⟩⟩ := ks
    have h := polar_unique (g := (cartanMul (⟨k, hk⟩, ⟨s, hs, hsJ⟩) : GL (Fin p ⊕ Fin q) ℂ))
      (k := ((k : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)) (p := s) hk hs rfl
    refine Prod.ext (Subtype.ext (Subtype.ext (Units.ext ?_))) (Subtype.ext ?_)
    · exact h.2
    · exact h.1
  right_inv g := Subtype.ext (Units.ext (polarUnitary_mul_polarPos (g : GL (Fin p ⊕ Fin q) ℂ)))
  continuous_toFun := by
    refine Continuous.mul (continuous_subtype_val.comp continuous_fst) ?_
    exact continuous_upqOfMatrix (continuous_subtype_val.comp continuous_snd) _
  continuous_invFun := by
    have hP : Continuous fun g : G => polarPos (g : GL (Fin p ⊕ Fin q) ℂ) :=
      (continuous_polarPos CFC.continuousOn_sqrt).comp continuous_subtype_val
    have hU : Continuous fun g : G => polarUnitary (g : GL (Fin p ⊕ Fin q) ℂ) :=
      continuous_coe_indefiniteUnitary.mul
        (continuousOn_matrix_inv.comp_continuous hP fun g => (polarPos_posDef _).isUnit)
    refine Continuous.prodMk ?_ (hP.subtype_mk _)
    exact (continuous_upqOfMatrix hU _).subtype_mk _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cartanHomeomorph_apply (ks : maxCompact G × cartanPos p q) :
    ((cartanHomeomorph ks : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) =
      (((ks.1 : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) * ks.2.1 := rfl

/- English proof (translation)
Use `⟨cartanHomeomorph.symm g, ?_, fun ks hks => ?_⟩` and prove the remaining obligations. Conclude with `congrArg (fun x : G => ((x : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)) (cartanHomeomorph.apply_symm_apply g)`. Apply `cartanHomeomorph.injective` to reduce the goal to its premises. Rewrite using `[Homeomorph.apply_symm_apply]`. Conclude with `Subtype.ext (Units.ext hks)`.
-/
theorem cartan_decomposition (g : G) :
    ∃! ks : maxCompact G × cartanPos p q,
      (((ks.1 : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) * ks.2.1 = ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) := by
  refine ⟨cartanHomeomorph.symm g, ?_, fun ks hks => ?_⟩
  · exact congrArg (fun x : G => ((x : GL (Fin p ⊕ Fin q) ℂ) : 𝔐))
      (cartanHomeomorph.apply_symm_apply g)
  · apply cartanHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (Units.ext hks)

end Polar

section MaxCompact

local notation "G" => indefiniteUnitaryGroup p q

/- English proof (translation)
The claim follows from `(isExpLieAlgebra_indefiniteUnitary p q).isClosed`.
-/
theorem isClosed_indefiniteUnitaryGroup : IsClosed (G : Set (GL (Fin p ⊕ Fin q) ℂ)) :=
  (isExpLieAlgebra_indefiniteUnitary p q).isClosed

/- English proof (translation)
The claim follows from `isCompact_maxCompact_of_isClosed isClosed_indefiniteUnitaryGroup`.
-/
theorem isCompact_maxCompact_indefiniteUnitary :
    IsCompact ((maxCompact G : Subgroup G) : Set G) :=
  isCompact_maxCompact_of_isClosed isClosed_indefiniteUnitaryGroup

instance : CompactSpace (maxCompact G) :=
  isCompact_iff_compactSpace.1 isCompact_maxCompact_indefiniteUnitary

/- English proof (translation)
Break down `isEmpty_or_nonempty n with hn | hn` into its components or cases. Use extensionality with `i`. Conclude with `isEmptyElim i`. Establish `hH` using `hP.isHermitian`. Establish `hu : IsUnit P` using `hP.isUnit`.

Establish `hle : ∀ A : Matrix n n ℂ, (∀ k : ℕ, ‖A ^ k‖ ≤ C) → ∀ z ∈ spectrum ℂ A, ‖z‖ ≤ 1`. Introduce `A hA z hz`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (C * ‖(1 : Matrix n n ℂ)‖) hlt`.

Establish `h` using `spectrum.norm_le_norm_mul_of_mem (spectrum.pow_mem_pow A k hz)`. Rewrite `h` using `[norm_pow]`. Establish `h1n : 0 ≤ ‖(1 : Matrix n n ℂ)‖` using `norm_nonneg _`. Use polynomial arithmetic with `[hA k]`. Establish `key : ∀ i, hH.eigenvalues i = 1`.

Introduce `i`. Use `set t := hH.eigenvalues i`. Establish `ht : 0 < t` using `hP.eigenvalues_pos i`. Establish `hmem : (t : ℂ) ∈ spectrum ℂ P`. Rewrite using `[hH.spectrum_eq_image_range]`.

Conclude with `⟨t, ⟨i, rfl⟩, rfl⟩`. Establish `hmem' : (t : ℂ)⁻¹ ∈ spectrum ℂ P⁻¹`. Use `(spectrum.inv₀_mem_iff (r := (t : ℂ)⁻¹) (a := hu.unit)).1 (by rw [inv_inv, IsUnit.unit_spec]; exact hmem)` as an intermediate fact. Rewrite `this` using `[Matrix.coe_units_inv, IsUnit.unit_spec]`. Then use the resulting hypothesis. Establish `a1` using `hle P h1 _ hmem`.

Establish `a2` using `hle P⁻¹ h2 _ hmem'`. Rewrite `a1` using `[Complex.norm_real, Real.norm_of_nonneg ht.le]`. Rewrite `a2` using `[norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, inv_le_one₀ ht]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hH.spectral_theorem]`.

Establish `: (RCLike.ofReal ∘ hH.eigenvalues : n → ℂ) = 1`. Use function extensionality and compare the values at `i`. Simplify using `[key i]`. Rewrite using `[this, Pi.one_def, diagonal_one, map_one]`.
-/
theorem eq_one_of_posDef_of_bounded {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : P.PosDef) {C : ℝ} (h1 : ∀ k : ℕ, ‖P ^ k‖ ≤ C)
    (h2 : ∀ k : ℕ, ‖P⁻¹ ^ k‖ ≤ C) : P = 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · ext i; exact isEmptyElim i
  have hH := hP.isHermitian
  have hu : IsUnit P := hP.isUnit
  have hle : ∀ A : Matrix n n ℂ, (∀ k : ℕ, ‖A ^ k‖ ≤ C) → ∀ z ∈ spectrum ℂ A, ‖z‖ ≤ 1 := by
    intro A hA z hz
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C * ‖(1 : Matrix n n ℂ)‖) hlt
    have h := spectrum.norm_le_norm_mul_of_mem (spectrum.pow_mem_pow A k hz)
    rw [norm_pow] at h
    have h1n : 0 ≤ ‖(1 : Matrix n n ℂ)‖ := norm_nonneg _
    nlinarith [hA k]
  have key : ∀ i, hH.eigenvalues i = 1 := by
    intro i
    set t := hH.eigenvalues i
    have ht : 0 < t := hP.eigenvalues_pos i
    have hmem : (t : ℂ) ∈ spectrum ℂ P := by
      rw [hH.spectrum_eq_image_range]
      exact ⟨t, ⟨i, rfl⟩, rfl⟩
    have hmem' : (t : ℂ)⁻¹ ∈ spectrum ℂ P⁻¹ := by
      have := (spectrum.inv₀_mem_iff (r := (t : ℂ)⁻¹) (a := hu.unit)).1
        (by rw [inv_inv, IsUnit.unit_spec]; exact hmem)
      rwa [Matrix.coe_units_inv, IsUnit.unit_spec] at this
    have a1 := hle P h1 _ hmem
    have a2 := hle P⁻¹ h2 _ hmem'
    rw [Complex.norm_real, Real.norm_of_nonneg ht.le] at a1
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, inv_le_one₀ ht] at a2
    linarith
  rw [hH.spectral_theorem]
  have : (RCLike.ofReal ∘ hH.eigenvalues : n → ℂ) = 1 := by
    funext i
    simp [key i]
  rw [this, Pi.one_def, diagonal_one, map_one]

/- English proof (translation)
Use `le_antisymm (fun g hg => ?_) hK` and prove the remaining obligations. Use `set ks := cartanHomeomorph.symm g`. Establish `hg' : g = cartanMul ks` using `(cartanHomeomorph.apply_symm_apply g).symm`. Use `set s : G := upqOfMatrix ks.2.1 ks.2.2.2`. Establish `hgs : g = (ks.1 : G) * s` using `hg'`.

Establish `hsmat : ((s : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) = ks.2.1` using `rfl`. Establish `hsL : s ∈ L`. Establish `: s = (ks.1 : G)⁻¹ * g` using `by rw [hgs, inv_mul_cancel_left]`. Rewrite using `[this]`. Conclude with `L.mul_mem (L.inv_mem (hK ks.1.2)) hg`.

Take `⟨C, hC⟩` from `(hL.image continuous_coe_indefiniteUnitary).isBounded.exists_norm_le`. Establish `hbd : ∀ x ∈ L, ‖((x : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)‖ ≤ C` using `fun x hx => hC _ ⟨x, hx, rfl⟩`. Establish `hs1 : ks.2.1 = 1`. Use `eq_one_of_posDef_of_bounded ks.2.2.1 (C := C) (fun k => ?_) (fun k => ?_)` and prove the remaining obligations. Use `hbd (s ^ k) (L.pow_mem hsL k)` as an intermediate fact.

Rewrite `this` using `[SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hsmat]`. Then use the resulting hypothesis. Use `hbd (s⁻¹ ^ k) (L.pow_mem (L.inv_mem hsL) k)` as an intermediate fact. Establish `hinv : (((s⁻¹ : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) = ks.2.1⁻¹`. Rewrite using `[Subgroup.coe_inv, Matrix.coe_units_inv, hsmat]`. Rewrite `this` using `[SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hinv]`. Then use the resulting hypothesis.

Establish `: s = 1` using `Subtype.ext (Units.ext hs1)`. Rewrite using `[hgs, this, mul_one]`. Conclude with `ks.1.2`.
-/
theorem eq_maxCompact_of_isCompact {L : Subgroup G} (hL : IsCompact (L : Set G))
    (hK : maxCompact G ≤ L) : L = maxCompact G := by
  refine le_antisymm (fun g hg => ?_) hK
  set ks := cartanHomeomorph.symm g
  have hg' : g = cartanMul ks := (cartanHomeomorph.apply_symm_apply g).symm
  set s : G := upqOfMatrix ks.2.1 ks.2.2.2
  have hgs : g = (ks.1 : G) * s := hg'
  have hsmat : ((s : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) = ks.2.1 := rfl
  have hsL : s ∈ L := by
    have : s = (ks.1 : G)⁻¹ * g := by rw [hgs, inv_mul_cancel_left]
    rw [this]
    exact L.mul_mem (L.inv_mem (hK ks.1.2)) hg

  obtain ⟨C, hC⟩ := (hL.image continuous_coe_indefiniteUnitary).isBounded.exists_norm_le
  have hbd : ∀ x ∈ L, ‖((x : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)‖ ≤ C := fun x hx => hC _ ⟨x, hx, rfl⟩
  have hs1 : ks.2.1 = 1 := by
    refine eq_one_of_posDef_of_bounded ks.2.2.1 (C := C) (fun k => ?_) (fun k => ?_)
    · have := hbd (s ^ k) (L.pow_mem hsL k)
      rwa [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hsmat] at this
    · have := hbd (s⁻¹ ^ k) (L.pow_mem (L.inv_mem hsL) k)
      have hinv : (((s⁻¹ : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) = ks.2.1⁻¹ := by
        rw [Subgroup.coe_inv, Matrix.coe_units_inv, hsmat]
      rwa [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hinv] at this
  have : s = 1 := Subtype.ext (Units.ext hs1)
  rw [hgs, this, mul_one]
  exact ks.1.2

/- English proof (translation)
Assemble the required witnesses or components as `⟨isCompact_maxCompact_indefiniteUnitary, fun _ hL hK => eq_maxCompact_of_isCompact hL hK⟩`.
-/
theorem isMaximalCompact_maxCompact :
    IsCompact ((maxCompact G : Subgroup G) : Set G) ∧
      ∀ L : Subgroup G, IsCompact (L : Set G) → maxCompact G ≤ L → L = maxCompact G :=
  ⟨isCompact_maxCompact_indefiniteUnitary, fun _ hL hK => eq_maxCompact_of_isCompact hL hK⟩

end MaxCompact

section Blocks

local notation "G" => indefiniteUnitaryGroup p q

/- English proof (translation)
Rewrite using `[indefJ, ← fromBlocks_diagonal, diagonal_one, ← diagonal_one, ← diagonal_neg]`. Both sides reduce to the same expression.
-/
theorem indefJ_eq_fromBlocks : J = fromBlocks 1 0 0 (-1) := by
  rw [indefJ, ← fromBlocks_diagonal, diagonal_one, ← diagonal_one, ← diagonal_neg]
  rfl

/- English proof (translation)
Establish `ha : (a : Matrix (Fin p) (Fin p) ℂ)ᴴ * a = 1`. Rewrite using `[← star_eq_conjTranspose]`. Conclude with `mem_unitaryGroup_iff'.1 a.2`. Establish `hb : (b : Matrix (Fin q) (Fin q) ℂ)ᴴ * b = 1`. Rewrite using `[← star_eq_conjTranspose]`.

Conclude with `mem_unitaryGroup_iff'.1 b.2`. Rewrite using `[indefJ_eq_fromBlocks, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `[ha, hb]`.
-/
theorem fromBlocks_preservesIndefJ (a : unitaryGroup (Fin p) ℂ) (b : unitaryGroup (Fin q) ℂ) :
    (fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 (b : Matrix (Fin q) (Fin q) ℂ))ᴴ * J *
      fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 (b : Matrix (Fin q) (Fin q) ℂ) = J := by
  have ha : (a : Matrix (Fin p) (Fin p) ℂ)ᴴ * a = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 a.2
  have hb : (b : Matrix (Fin q) (Fin q) ℂ)ᴴ * b = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 b.2
  rw [indefJ_eq_fromBlocks, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [ha, hb]

/- English proof (translation)
Rewrite using `[mem_unitaryGroup_iff', star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]`. Establish `ha : (a : Matrix (Fin p) (Fin p) ℂ)ᴴ * a = 1`. Rewrite using `[← star_eq_conjTranspose]`. Conclude with `mem_unitaryGroup_iff'.1 a.2`. Establish `hb : (b : Matrix (Fin q) (Fin q) ℂ)ᴴ * b = 1`.

Rewrite using `[← star_eq_conjTranspose]`. Conclude with `mem_unitaryGroup_iff'.1 b.2`. Simplify using `[ha, hb, fromBlocks_one]`.
-/
theorem fromBlocks_mem_unitaryGroup (a : unitaryGroup (Fin p) ℂ) (b : unitaryGroup (Fin q) ℂ) :
    fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 (b : Matrix (Fin q) (Fin q) ℂ) ∈
      unitaryGroup (Fin p ⊕ Fin q) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]
  have ha : (a : Matrix (Fin p) (Fin p) ℂ)ᴴ * a = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 a.2
  have hb : (b : Matrix (Fin q) (Fin q) ℂ)ᴴ * b = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 b.2
  simp [ha, hb, fromBlocks_one]

def blockDiagK (ab : unitaryGroup (Fin p) ℂ × unitaryGroup (Fin q) ℂ) : maxCompact G :=
  ⟨upqOfMatrix _ (fromBlocks_preservesIndefJ ab.1 ab.2), fromBlocks_mem_unitaryGroup ab.1 ab.2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_blockDiagK (ab : unitaryGroup (Fin p) ℂ × unitaryGroup (Fin q) ℂ) :
    ((((blockDiagK ab : maxCompact G) : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) =
      fromBlocks (ab.1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (ab.2 : Matrix (Fin q) (Fin q) ℂ) := rfl

/- English proof (translation)
Take `⟨hu, h12, h21⟩` from `mem_maxCompact_indefiniteUnitary.1 k.2`. Use `set m := (((k : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)`. Establish `hm : m = fromBlocks m.toBlocks₁₁ 0 0 m.toBlocks₂₂`. Rewrite using `[← h12, ← h21, fromBlocks_toBlocks]`. Establish `h` using `mem_unitaryGroup_iff'.1 hu`.

Rewrite `h` using `[star_eq_conjTranspose, hm, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]`. Simplify using `only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h`. Conclude with `⟨mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact h.1), mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact h.2.2.2)⟩`.
-/
theorem toBlocks_mem_unitaryGroup (k : maxCompact G) :
    (((k : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐).toBlocks₁₁ ∈ unitaryGroup (Fin p) ℂ ∧
      (((k : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐).toBlocks₂₂ ∈ unitaryGroup (Fin q) ℂ := by
  obtain ⟨hu, h12, h21⟩ := mem_maxCompact_indefiniteUnitary.1 k.2
  set m := (((k : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)
  have hm : m = fromBlocks m.toBlocks₁₁ 0 0 m.toBlocks₂₂ := by
    rw [← h12, ← h21, fromBlocks_toBlocks]
  have h := mem_unitaryGroup_iff'.1 hu
  rw [star_eq_conjTranspose, hm, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_inj] at h
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact ⟨mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact h.1),
    mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact h.2.2.2)⟩

noncomputable def maxCompactEquivProd :
    unitaryGroup (Fin p) ℂ × unitaryGroup (Fin q) ℂ ≃ₜ* maxCompact G where
  toFun := blockDiagK
  invFun k := (⟨_, (toBlocks_mem_unitaryGroup k).1⟩, ⟨_, (toBlocks_mem_unitaryGroup k).2⟩)
  left_inv ab := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact toBlocks_fromBlocks₁₁ _ _ _ _
    · exact toBlocks_fromBlocks₂₂ _ _ _ _
  right_inv k := by
    obtain ⟨hu, h12, h21⟩ := mem_maxCompact_indefiniteUnitary.1 k.2
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    rw [coe_blockDiagK]
    simp only
    rw [← h12, ← h21, fromBlocks_toBlocks]
  map_mul' a b := by
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    simp only [Subgroup.coe_mul, Units.val_mul, coe_blockDiagK, Prod.fst_mul, Prod.snd_mul,
      Submonoid.coe_mul, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add]
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_upqOfMatrix ?_ _) _
    exact Continuous.matrix_fromBlocks (continuous_subtype_val.comp continuous_fst)
      continuous_const continuous_const (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hk : Continuous fun k : maxCompact G => (((k : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) :=
      continuous_coe_indefiniteUnitary.comp continuous_subtype_val
    exact Continuous.prodMk ((hk.matrix_submatrix _ _).subtype_mk _)
      ((hk.matrix_submatrix _ _).subtype_mk _)

end Blocks

section Topology

local notation "G" => indefiniteUnitaryGroup p q

/- English proof (translation)
Use extensionality with `m`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `g.2`. Introduce `hm`.

Conclude with `⟨upqOfMatrix m hm, rfl⟩`.
-/
theorem range_coe_indefiniteUnitary :
    Set.range (fun g : G => ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)) = {m | mᴴ * J * m = J} := by
  ext m
  constructor
  · rintro ⟨g, rfl⟩
    exact g.2
  · intro hm
    exact ⟨upqOfMatrix m hm, rfl⟩

/- English proof (translation)
Use `⟨Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal, ?_⟩` and prove the remaining obligations. Rewrite using `[range_coe_indefiniteUnitary]`. Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`.
-/
theorem isClosedEmbedding_coe_indefiniteUnitary :
    Topology.IsClosedEmbedding (fun g : G => ((g : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)) := by
  refine ⟨Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal, ?_⟩
  rw [range_coe_indefiniteUnitary]
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

instance : T2Space G := isClosedEmbedding_coe_indefiniteUnitary.isEmbedding.t2Space

instance : LocallyCompactSpace G := isClosedEmbedding_coe_indefiniteUnitary.locallyCompactSpace

instance : SecondCountableTopology G :=
  isClosedEmbedding_coe_indefiniteUnitary.isEmbedding.isInducing.secondCountableTopology

end Topology

end GroundTheory.Heights₂.Theta
