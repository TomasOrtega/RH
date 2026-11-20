import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommuteOfCommuteSeparableCharpolyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsotropicIdempotentCentralizerHermitianStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactPreimageMulStarAnisotropicSubmoduleStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.NormSec

/- English proof (translation)
Introduce `F E _ _ _ _ hU r A₀ hA hsep M hM`. Establish `hA' : star A₀ = A₀` using `by rw [Matrix.star_eq_conjTranspose]; exact hA`. Take `⟨f, hfA, hff, hffs, haniso⟩` from `GlobalTheory.T.exists_isotropic_idempotent_centralizer_hermitian E r A₀ hA hsep`. Establish `hcomm` using `GlobalTheory.T.matrix_commute_of_commute_separable_charpoly E r A₀ hsep`. Establish `hstarC : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → star m * A₀ = A₀ * star m`.

Introduce `m hm`. Use `congrArg star hm` as an intermediate fact. Rewrite `this` using `[star_mul, star_mul, hA']`. Conclude with `this.symm`. Use `set g := star f with hg`.

Use `set e : Matrix (Fin r) (Fin r) E := 1 - f - g with he`. Establish `hes : star e = 1 - g - f` using `by rw [he, star_sub, star_sub, star_one, hg, star_star]`. Set `R` to `Subring.centralizer ({A₀} : Set (Matrix (Fin r) (Fin r) E))`. Establish `memR : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → m ∈ R`. Introduce `m hm`.

Rewrite using `[Subring.mem_centralizer_iff]`. Introduce `x hx`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `hm.symm`. Establish `memR' : ∀ m ∈ R, m * A₀ = A₀ * m`.

Introduce `m hm`. Conclude with `((Subring.mem_centralizer_iff.1 hm) A₀ rfl).symm`. Use `letI : CommRing R := { (inferInstance : Ring R) with mul_comm := fun a b => Subtype.ext (hcomm a.1 b.1 (memR' _ a.2) (memR' _ b.2)) }`. Set `V : Submodule E (Matrix (Fin r) (Fin r) E)` to `{ carrier := {z | z * A₀ = A₀ * z ∧ z * e = z} add_mem' := by`. Introduce and unpack `a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩`.

Conclude with `⟨by rw [add_mul, mul_add, ha1, hb1], by rw [add_mul, ha2, hb2]⟩`. Use the proof step `zero_mem' := ⟨by simp, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨ha1, ha2⟩`. Conclude with `⟨by rw [Matrix.smul_mul, Matrix.mul_smul, ha1], by rw [Matrix.smul_mul, ha2]⟩ }`.

Establish `hV : ∀ z ∈ V, z * star z = 0 → z = 0`. Introduce and unpack `z ⟨hz1, hz2⟩ h0`. Establish `h` using `haniso z hz1`. Rewrite `h` using `[hz2]`. Conclude with `h h0`.

Set `M₁` to `(fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) '' M`. Set `M₂` to `(fun u : GL (Fin r) E => ((u⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) '' M`. Establish `hM₁ : IsCompact M₁` using `hM.image Units.continuous_val`. Establish `hM₂ : IsCompact M₂` using `hM.image Units.continuous_coe_inv`. Set `B₁` to `(fun x => x * e) '' M₁`.

Set `B₂` to `(fun x => x * e) '' M₂`. Establish `hB₁ : IsCompact B₁` using `hM₁.image (continuous_mul_right e)`. Establish `hB₂ : IsCompact B₂` using `hM₂.image (continuous_mul_right e)`. Establish `hT₁` using `GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₁ hB₁`. Establish `hT₂` using `GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₂ hB₂`.

Set `P₁` to `(fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) '' ({z | z ∈ V ∧ z * star z ∈ B₁} ×ˢ M₁)`. Set `P₂` to `(fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) '' ({z | z ∈ V ∧ z * star z ∈ B₂} ×ˢ M₂)`. Establish `hP₁ : IsCompact P₁` using `(hT₁.prod hM₁).image (by fun_prop)`. Establish `hP₂ : IsCompact P₂` using `(hT₂.prod hM₂).image (by fun_prop)`. Use `⟨{s | (s : Matrix (Fin r) (Fin r) E) ∈ P₁ ∧ ((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ P₂}, ?_, ?_⟩` and prove the remaining obligations.

Use `Units.isClosedEmbedding_embedProduct.isCompact_preimage (hP₁.prod (hP₂.image MulOpposite.continuous_op))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `s`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]`. Rewrite using `[MulOpposite.op_injective.mem_set_image]`.

Introduce and unpack `t ht ⟨m, hmM, hm⟩`. Use `set T : Matrix (Fin r) (Fin r) E := (t : Matrix (Fin r) (Fin r) E) with hT`. Use `set Ti : Matrix (Fin r) (Fin r) E := ((t⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hTi`. Use `set mm : Matrix (Fin r) (Fin r) E := (m : Matrix (Fin r) (Fin r) E) with hmm`. Use `set mi : Matrix (Fin r) (Fin r) E := ((m⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hmi`.

Establish `cTi : Ti * A₀ = A₀ * Ti` using `Commute.units_inv_left (u := t) ht`. Establish `cm : mm * A₀ = A₀ * mm`. Rewrite using `[← hm, mul_assoc, hstarC _ ht, ← mul_assoc, ht, mul_assoc]`. Establish `cmi : mi * A₀ = A₀ * mi` using `Commute.units_inv_left (u := m) cm`. Set `xT : R` to `⟨T, memR _ ht⟩`.

Set `xTp : R` to `⟨star T, memR _ (hstarC _ ht)⟩`. Set `xTi : R` to `⟨Ti, memR _ cTi⟩`. Set `xTip : R` to `⟨star Ti, memR _ (hstarC _ cTi)⟩`. Set `xmi : R` to `⟨mi, memR _ cmi⟩`. Set `xf : R` to `⟨f, memR _ hfA⟩`.

Set `xg : R` to `⟨g, memR _ (hstarC _ hfA)⟩`. Establish `hfR : xf * xf = xf` using `Subtype.ext hff`. Establish `hgR : xg * xg = xg` using `Subtype.ext (by show star f * star f = star f; rw [← star_mul, hff])`. Establish `hfgR : xf * xg = 0` using `Subtype.ext hffs`. Establish `hTiR : xT * xTi = 1` using `Subtype.ext (Units.mul_inv t)`.

Establish `hTpiR : xTp * xTip = 1` using `Subtype.ext (by show star T * star Ti = 1`. Rewrite using `[← star_mul, hT, hTi, Units.inv_mul, star_one])`. Establish `hmiR : xmi * (xT * xTp) = 1` using `Subtype.ext (by show mi * (T * star T) = 1`. Rewrite using `[hm, hmi, hmm, Units.inv_mul])`. Establish `heR : (1 - xf - xg) * (1 - xf - xg) = 1 - xf - xg` using `by linear_combination hfR + hgR + 2 * hfgR`.

Establish `hefR : (1 - xf - xg) * xf = 0` using `by linear_combination -hfR - hfgR`. Establish `hegR : (1 - xf - xg) * xg = 0` using `by linear_combination -hgR - hfgR`. Set `X₀ : R` to `xT * (1 - xf - xg) + xT * xTp * xf + xg`. Set `X₁ : R` to `xTi * (1 - xf - xg) + xmi * xf + xg`. Establish `h01 : X₀ * X₁ = 1`.

Take the linear combination `(1 - xf - xg) * (1 - xf - xg) * hTiR + heR + xT * xmi * hefR + xT * hegR + xT * xTp * xTi * hefR + xf * xf * hmiR + hfR + xT * xTp * hfgR + xTi * hegR + xmi * hfgR + hgR`. Establish `h10 : X₁ * X₀ = 1` using `by rw [mul_comm]; exact h01`. Set `s : GL (Fin r) E` to `⟨X₀.1, X₁.1, congrArg Subtype.val h01, congrArg Subtype.val h10⟩`. Establish `hX₀ : X₀.1 = T * e + mm * f + g` using `by show T * (1 - f - g) + T * star T * f + g = _`. Rewrite using `[hm]`.

Establish `hX₁ : X₁.1 = Ti * e + mi * f + g` using `rfl`. Use `⟨s, ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `⟨(T * e, mm), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₀.symm⟩` and prove the remaining obligations. Conclude with `memR' _ (xT * (1 - xf - xg)).2`. Establish `: xT * (1 - xf - xg) * (1 - xf - xg) = xT * (1 - xf - xg)` using `by linear_combination xT * heR`.

Conclude with `congrArg Subtype.val this`. Use `⟨mm, ⟨m, hmM, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `: xT * xTp * (1 - xf - xg) = xT * (1 - xf - xg) * ((1 - xg - xf) * xTp)`. Take the linear combination `(-(xT * xTp)) * heR`. Establish `h2` using `congrArg Subtype.val this`.

Use `show mm * e = T * e * star (T * e)`. Rewrite using `[star_mul, hes, ← hm]`. Conclude with `h2`. Use `⟨(Ti * e, mi), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₁.symm⟩` and prove the remaining obligations. Conclude with `memR' _ (xTi * (1 - xf - xg)).2`.

Establish `: xTi * (1 - xf - xg) * (1 - xf - xg) = xTi * (1 - xf - xg)` using `by linear_combination xTi * heR`. Conclude with `congrArg Subtype.val this`. Use `⟨mi, ⟨m, hmM, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hTT : xTi * xTip = xmi`. Take the linear combination `(-(xTi * xTip)) * hmiR + xmi * xTp * xTip * hTiR + xmi * hTpiR`.

Establish `: xmi * (1 - xf - xg) = xTi * (1 - xf - xg) * ((1 - xg - xf) * xTip)`. Take the linear combination `(-(xTi * xTip)) * heR - (1 - xf - xg) * hTT`. Establish `h2` using `congrArg Subtype.val this`. Use `show mi * e = Ti * e * star (Ti * e)`. Rewrite using `[star_mul, hes]`.

Conclude with `h2`. Conclude with `memR' _ X₀.2`. Establish `: X₀ * ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf) = xT * xTp`. Take the linear combination `xT * xTp * heR + xT ^ 2 * xTp * hegR + xT * hefR + xT * xTp ^ 2 * hefR + xT ^ 2 * xTp ^ 2 * hfgR + xT * xTp * hfR + xTp * hegR + xT * xTp * hgR + hfgR`. Establish `h2` using `congrArg Subtype.val this`.

Establish `hst : star X₀.1 = ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf).1` using `by show star (T * (1 - f - g) + T * star T * f + g) = (1 - g - f) * star T + g * (T * star T) + f`. Rewrite using `[hg]`. Simplify using `only [star_add, star_mul, star_sub, star_one, star_star]`. Use `show X₀.1 * star X₀.1 = T * star T`. Rewrite using `[hst]`.

Conclude with `h2`.
-/
theorem normsec : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) := by
  intro F E _ _ _ _ hU r A₀ hA hsep M hM
  classical
  have hA' : star A₀ = A₀ := by rw [Matrix.star_eq_conjTranspose]; exact hA
  obtain ⟨f, hfA, hff, hffs, haniso⟩ := GlobalTheory.T.exists_isotropic_idempotent_centralizer_hermitian E r A₀ hA hsep
  have hcomm := GlobalTheory.T.matrix_commute_of_commute_separable_charpoly E r A₀ hsep
  have hstarC : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → star m * A₀ = A₀ * star m := by
    intro m hm
    have := congrArg star hm
    rw [star_mul, star_mul, hA'] at this
    exact this.symm
  set g := star f with hg
  set e : Matrix (Fin r) (Fin r) E := 1 - f - g with he
  have hes : star e = 1 - g - f := by rw [he, star_sub, star_sub, star_one, hg, star_star]
  let R := Subring.centralizer ({A₀} : Set (Matrix (Fin r) (Fin r) E))
  have memR : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → m ∈ R := by
    intro m hm
    rw [Subring.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact hm.symm
  have memR' : ∀ m ∈ R, m * A₀ = A₀ * m := by
    intro m hm
    exact ((Subring.mem_centralizer_iff.1 hm) A₀ rfl).symm
  letI : CommRing R := { (inferInstance : Ring R) with
    mul_comm := fun a b => Subtype.ext (hcomm a.1 b.1 (memR' _ a.2) (memR' _ b.2)) }
  let V : Submodule E (Matrix (Fin r) (Fin r) E) :=
    { carrier := {z | z * A₀ = A₀ * z ∧ z * e = z}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by rw [add_mul, mul_add, ha1, hb1], by rw [add_mul, ha2, hb2]⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        exact ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, ha1], by rw [Matrix.smul_mul, ha2]⟩ }
  have hV : ∀ z ∈ V, z * star z = 0 → z = 0 := by
    rintro z ⟨hz1, hz2⟩ h0
    have h := haniso z hz1
    rw [hz2] at h
    exact h h0
  let M₁ := (fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) '' M
  let M₂ := (fun u : GL (Fin r) E => ((u⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) '' M
  have hM₁ : IsCompact M₁ := hM.image Units.continuous_val
  have hM₂ : IsCompact M₂ := hM.image Units.continuous_coe_inv
  let B₁ := (fun x => x * e) '' M₁
  let B₂ := (fun x => x * e) '' M₂
  have hB₁ : IsCompact B₁ := hM₁.image (continuous_mul_right e)
  have hB₂ : IsCompact B₂ := hM₂.image (continuous_mul_right e)
  have hT₁ := GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₁ hB₁
  have hT₂ := GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₂ hB₂
  let P₁ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₁} ×ˢ M₁)
  let P₂ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₂} ×ˢ M₂)
  have hP₁ : IsCompact P₁ := (hT₁.prod hM₁).image (by fun_prop)
  have hP₂ : IsCompact P₂ := (hT₂.prod hM₂).image (by fun_prop)
  refine ⟨{s | (s : Matrix (Fin r) (Fin r) E) ∈ P₁ ∧ ((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ P₂}, ?_, ?_⟩
  · have := Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hP₁.prod (hP₂.image MulOpposite.continuous_op))
    convert this using 1
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
    rw [MulOpposite.op_injective.mem_set_image]
  rintro t ht ⟨m, hmM, hm⟩
  set T : Matrix (Fin r) (Fin r) E := (t : Matrix (Fin r) (Fin r) E) with hT
  set Ti : Matrix (Fin r) (Fin r) E := ((t⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hTi
  set mm : Matrix (Fin r) (Fin r) E := (m : Matrix (Fin r) (Fin r) E) with hmm
  set mi : Matrix (Fin r) (Fin r) E := ((m⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hmi
  have cTi : Ti * A₀ = A₀ * Ti := Commute.units_inv_left (u := t) ht
  have cm : mm * A₀ = A₀ * mm := by
    rw [← hm, mul_assoc, hstarC _ ht, ← mul_assoc, ht, mul_assoc]
  have cmi : mi * A₀ = A₀ * mi := Commute.units_inv_left (u := m) cm
  let xT : R := ⟨T, memR _ ht⟩
  let xTp : R := ⟨star T, memR _ (hstarC _ ht)⟩
  let xTi : R := ⟨Ti, memR _ cTi⟩
  let xTip : R := ⟨star Ti, memR _ (hstarC _ cTi)⟩
  let xmi : R := ⟨mi, memR _ cmi⟩
  let xf : R := ⟨f, memR _ hfA⟩
  let xg : R := ⟨g, memR _ (hstarC _ hfA)⟩
  have hfR : xf * xf = xf := Subtype.ext hff
  have hgR : xg * xg = xg := Subtype.ext (by show star f * star f = star f; rw [← star_mul, hff])
  have hfgR : xf * xg = 0 := Subtype.ext hffs
  have hTiR : xT * xTi = 1 := Subtype.ext (Units.mul_inv t)
  have hTpiR : xTp * xTip = 1 := Subtype.ext (by
    show star T * star Ti = 1
    rw [← star_mul, hT, hTi, Units.inv_mul, star_one])
  have hmiR : xmi * (xT * xTp) = 1 := Subtype.ext (by
    show mi * (T * star T) = 1
    rw [hm, hmi, hmm, Units.inv_mul])
  have heR : (1 - xf - xg) * (1 - xf - xg) = 1 - xf - xg := by linear_combination hfR + hgR + 2 * hfgR
  have hefR : (1 - xf - xg) * xf = 0 := by linear_combination -hfR - hfgR
  have hegR : (1 - xf - xg) * xg = 0 := by linear_combination -hgR - hfgR
  let X₀ : R := xT * (1 - xf - xg) + xT * xTp * xf + xg
  let X₁ : R := xTi * (1 - xf - xg) + xmi * xf + xg
  have h01 : X₀ * X₁ = 1 := by
    linear_combination (1 - xf - xg) * (1 - xf - xg) * hTiR + heR + xT * xmi * hefR + xT * hegR +
      xT * xTp * xTi * hefR + xf * xf * hmiR + hfR + xT * xTp * hfgR + xTi * hegR + xmi * hfgR + hgR
  have h10 : X₁ * X₀ = 1 := by rw [mul_comm]; exact h01
  let s : GL (Fin r) E := ⟨X₀.1, X₁.1, congrArg Subtype.val h01, congrArg Subtype.val h10⟩
  have hX₀ : X₀.1 = T * e + mm * f + g := by
    show T * (1 - f - g) + T * star T * f + g = _
    rw [hm]
  have hX₁ : X₁.1 = Ti * e + mi * f + g := rfl
  refine ⟨s, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine ⟨(T * e, mm), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₀.symm⟩
    · exact memR' _ (xT * (1 - xf - xg)).2
    · have : xT * (1 - xf - xg) * (1 - xf - xg) = xT * (1 - xf - xg) := by linear_combination xT * heR
      exact congrArg Subtype.val this
    · refine ⟨mm, ⟨m, hmM, rfl⟩, ?_⟩
      have : xT * xTp * (1 - xf - xg) = xT * (1 - xf - xg) * ((1 - xg - xf) * xTp) := by
        linear_combination (-(xT * xTp)) * heR
      have h2 := congrArg Subtype.val this
      show mm * e = T * e * star (T * e)
      rw [star_mul, hes, ← hm]
      exact h2
  · refine ⟨(Ti * e, mi), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₁.symm⟩
    · exact memR' _ (xTi * (1 - xf - xg)).2
    · have : xTi * (1 - xf - xg) * (1 - xf - xg) = xTi * (1 - xf - xg) := by linear_combination xTi * heR
      exact congrArg Subtype.val this
    · refine ⟨mi, ⟨m, hmM, rfl⟩, ?_⟩
      have hTT : xTi * xTip = xmi := by
        linear_combination (-(xTi * xTip)) * hmiR + xmi * xTp * xTip * hTiR + xmi * hTpiR
      have : xmi * (1 - xf - xg) = xTi * (1 - xf - xg) * ((1 - xg - xf) * xTip) := by
        linear_combination (-(xTi * xTip)) * heR - (1 - xf - xg) * hTT
      have h2 := congrArg Subtype.val this
      show mi * e = Ti * e * star (Ti * e)
      rw [star_mul, hes]
      exact h2
  · exact memR' _ X₀.2
  · have : X₀ * ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf) = xT * xTp := by
      linear_combination xT * xTp * heR + xT ^ 2 * xTp * hegR + xT * hefR + xT * xTp ^ 2 * hefR +
        xT ^ 2 * xTp ^ 2 * hfgR + xT * xTp * hfR + xTp * hegR + xT * xTp * hgR + hfgR
    have h2 := congrArg Subtype.val this
    have hst : star X₀.1 = ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf).1 := by
      show star (T * (1 - f - g) + T * star T * f + g) = (1 - g - f) * star T + g * (T * star T) + f
      rw [hg]
      simp only [star_add, star_mul, star_sub, star_one, star_star]
    show X₀.1 * star X₀.1 = T * star T
    rw [hst]
    exact h2

end GlobalTheory.NormSec
