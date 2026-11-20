import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodPtsModel

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GoodPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem inV_iff_val (T : CDVR) (x : T.Fr) : InV T x ↔ valV T.V x ≤ 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact HeightOneSpectrum.valuation_le_one _ a
  · intro h
    exact IsDiscreteValuationRing.exists_lift_of_le_one h

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem inV_iff_vV (T : CDVR) {x : T.Fr} (hx : x ≠ 0) : InV T x ↔ 0 ≤ vV T.V x := by
  have h0 : valV T.V x ≠ 0 := (valV T.V).ne_zero_iff.mpr hx
  rw [inV_iff_val, vV, neg_nonneg, WithZero.log_le_iff_le_exp h0, WithZero.exp_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem inV_iff_nval (T : CDVR) {e : ℕ} (he : 0 < e) (x : T.Fr) : InV T x ↔ 0 ≤ nval T.V e x := by
  unfold nval
  by_cases hx : x = 0
  · subst hx
    rw [if_pos rfl]
    exact iff_of_true (algebraMap T.V T.Fr).range.zero_mem le_top
  · rw [if_neg hx, inV_iff_vV T hx, EReal.coe_nonneg, le_div_iff₀ (by exact_mod_cast he), zero_mul,
      Int.cast_nonneg_iff]

variable {la : HeightOneSpectrum (𝓞 c.F)}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem bddGood_of_bddAll {κ : c.F} {f : Rul Xo c} (h : BddAll Xo c la κ f) : BddGood Xo c la κ f := by
  intro T io e ho y hy _
  exact h T io e ho y hy

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem bddAll_iff_smul (κ : c.F) (f : Rul Xo c) : BddAll Xo c la κ f ↔ BddAll Xo c la 1 (κ • f) := by
  unfold BddAll
  simp only [map_one, one_mul, evI_smul]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem bddGood_iff_smul (κ : c.F) (f : Rul Xo c) : BddGood Xo c la κ f ↔ BddGood Xo c la 1 (κ • f) := by
  unfold BddGood
  simp only [map_one, one_mul, evI_smul]

/- English proof (translation)
Equip the data with the indicated structure. A detailed English derivation is pending.
-/
theorem evI_one {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) : evI y 1 = 1 := by
  letI := io.toAlgebra
  exact evalAt_one _ _ _ y.2.1

/- English proof (translation)
Equip the data with the indicated structure. A detailed English derivation is pending.
-/
private theorem evI_add_non_galois_descent {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (f g : Rul Xo c) :
    evI y (f + g) = evI y f + evI y g := by
  letI := io.toAlgebra
  exact evalAt_add _ _ f g _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bddAll_add {κ : c.F} {f g : Rul Xo c} (hf : BddAll Xo c la κ f) (hg : BddAll Xo c la κ g) :
    BddAll Xo c la κ (f + g) := by
  intro T io e ho y hy
  rw [evI_add_non_galois_descent, mul_add]
  exact (algebraMap T.V T.Fr).range.add_mem (hf T io e ho y hy) (hg T io e ho y hy)

/- English proof (translation)
Equip the data with the indicated structure. A detailed English derivation is pending.
-/
private theorem evI_mul_non_galois_descent {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (f g : Rul Xo c) :
    evI y (f * g) = evI y f * evI y g := by
  letI := io.toAlgebra
  exact evalAt_mul _ _ f g _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bddAll_mul {κ μ : c.F} {f g : Rul Xo c} (hf : BddAll Xo c la κ f) (hg : BddAll Xo c la μ g) :
    BddAll Xo c la (κ * μ) (f * g) := by
  intro T io e ho y hy
  rw [evI_mul_non_galois_descent, map_mul, mul_mul_mul_comm]
  exact (algebraMap T.V T.Fr).range.mul_mem (hf T io e ho y hy) (hg T io e ho y hy)

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem inV_io {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {a : c.F} (ha : a ≠ 0) :
    InV T (io a) ↔ 0 ≤ vLa la a := by
  obtain ⟨he, hv⟩ := ho
  rw [inV_iff_vV T ((map_ne_zero io).mpr ha), hv a]
  exact mul_nonneg_iff_of_pos_left (by exact_mod_cast he)

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem smul_mem_supSet {W : Submodule c.F (Rul Xo c)} {a : c.F} (ha : 0 ≤ vLa la a) {f : Rul Xo c}
    (hf : f ∈ supSet Xo c la W) : a • f ∈ supSet Xo c la W := by
  obtain ⟨hW, hb⟩ := hf
  show a • f ∈ W ∧ BddAll Xo c la 1 (a • f)
  refine ⟨W.smul_mem a hW, ?_⟩
  intro T io e ho y hy
  have h1 := hb T io e ho y hy
  rw [map_one, one_mul] at h1
  rw [map_one, one_mul, evI_smul]
  have h2 : InV T (io a) := by
    by_cases ha0 : a = 0
    · rw [ha0, map_zero]
      exact (algebraMap T.V T.Fr).range.zero_mem
    · exact (inV_io ho ha0).mpr ha
  exact (algebraMap T.V T.Fr).range.mul_mem h2 h1

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem add_mem_supSet {W : Submodule c.F (Rul Xo c)} {f g : Rul Xo c}
    (hf : f ∈ supSet Xo c la W) (hg : g ∈ supSet Xo c la W) : f + g ∈ supSet Xo c la W := by
  obtain ⟨hfW, hfb⟩ := hf
  obtain ⟨hgW, hgb⟩ := hg
  show f + g ∈ W ∧ BddAll Xo c la 1 (f + g)
  exact ⟨W.add_mem hfW hgW, bddAll_add hfb hgb⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bddAll_one_iff (hne : IntFrNe Xo c (fun _ _ y => y.IsAlg)) {κ : c.F} (hκ : κ ≠ 0) :
    BddAll Xo c la κ 1 ↔ 0 ≤ vLa la κ := by
  constructor
  · intro h
    obtain ⟨T, io, e, ho, y, hy⟩ := hne la
    have h1 := h T io e ho y hy
    rw [evI_one, mul_one] at h1
    exact (inV_io ho hκ).mp h1
  · intro h T io e ho y _
    rw [evI_one, mul_one]
    exact (inV_io ho hκ).mpr h

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem vV_mul' (T : CDVR) {a b : T.Fr} (ha : a ≠ 0) (hb : b ≠ 0) :
    vV T.V (a * b) = vV T.V a + vV T.V b := by
  rw [vV, vV, vV, map_mul, WithZero.log_mul ((valV T.V).ne_zero_iff.mpr ha)
    ((valV T.V).ne_zero_iff.mpr hb), neg_add]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem inV_mul_iff_vLa_add_nval_nonneg {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    {κ : c.F} (hκ : κ ≠ 0) (z : T.Fr) :
    InV T (io κ * z) ↔ 0 ≤ (((vLa la κ : ℤ) : ℝ) : EReal) + nval T.V e z := by
  obtain ⟨he, hv⟩ := ho
  have hk : io κ ≠ 0 := (map_ne_zero io).mpr hκ
  by_cases hz : z = 0
  · subst hz
    rw [mul_zero]
    unfold nval
    rw [if_pos rfl, EReal.coe_add_top]
    exact iff_of_true (algebraMap T.V T.Fr).range.zero_mem le_top
  · have he' : (0 : ℝ) < e := by exact_mod_cast he
    rw [inV_iff_vV T (mul_ne_zero hk hz), vV_mul' T hk hz, hv κ, nval, if_neg hz,
      ← EReal.coe_add, EReal.coe_nonneg,
      show ((vLa la κ : ℤ) : ℝ) + (vV T.V z : ℝ) / e = (((e : ℤ) * vLa la κ + vV T.V z : ℤ) : ℝ) / e by
        push_cast; field_simp,
      le_div_iff₀ he', zero_mul, Int.cast_nonneg_iff]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem bddAll_iff_vAtV {κ : c.F} (hκ : κ ≠ 0) (f : Rul Xo c) :
    BddAll Xo c la κ f ↔
      ∀ y : PtV Xo c (fun _ _ y => y.IsAlg) Unit (fun _ _ _ _ => True) la,
        0 ≤ (((vLa la κ : ℤ) : ℝ) : EReal) + vAtV y f := by
  constructor
  · rintro h ⟨q, T, io, e, ho, y, hy, eta, -, rfl⟩
    exact (inV_mul_iff_vLa_add_nval_nonneg ho hκ _).mp (h T io e ho y hy)
  · intro h T io e ho y hy
    exact (inV_mul_iff_vLa_add_nval_nonneg ho hκ _).mpr (h (Subtype.mk _ ⟨T, io, e, ho, y, hy, (), trivial, rfl⟩))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem bddGood_iff_vAtV {κ : c.F} (hκ : κ ≠ 0) (f : Rul Xo c) :
    BddGood Xo c la κ f ↔
      ∀ y : PtV Xo c (fun _ _ y => y.IsAlg ∧ Good y) Unit (fun _ _ _ _ => True) la,
        0 ≤ (((vLa la κ : ℤ) : ℝ) : EReal) + vAtV y f := by
  constructor
  · rintro h ⟨q, T, io, e, ho, y, ⟨hy, hg⟩, eta, -, rfl⟩
    exact (inV_mul_iff_vLa_add_nval_nonneg ho hκ _).mp (h T io e ho y hy hg)
  · intro h T io e ho y hy hg
    exact (inV_mul_iff_vLa_add_nval_nonneg ho hκ _).mpr (h (Subtype.mk _ ⟨T, io, e, ho, y, ⟨hy, hg⟩, (), trivial, rfl⟩))

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem good_congr {T : CDVR} {io : c.F →+* T.Fr} {y y' : IntFr Xo c T io}
    (h : (letI := io.toAlgebra; y.1.x) = (letI := io.toAlgebra; y'.1.x)) (hy : Good y) : Good y' := by
  unfold Good at hy ⊢
  obtain ⟨G, t', m₁, m₂, hp⟩ := hy
  exact ⟨G, t', h ▸ m₁, m₂, hp⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem good_iff_abelian {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) :
    Good y ↔ ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr))
      (_ : SABMap t' Xo.univ.t (letI := io.toAlgebra; y.1.x))
      (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), IsAbelianScheme G.G := by
  unfold Good
  constructor
  · rintro ⟨G, t', m₁, m₂, hp⟩
    obtain ⟨hc, hs, -, -, hg, -⟩ := G.semi
    exact ⟨G, t', m₁, m₂, ⟨hc, hs, hp, hg⟩⟩
  · rintro ⟨G, t', m₁, m₂, ha⟩
    exact ⟨G, t', m₁, m₂, ha.proper⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bddGood_one_iff (hne : IntFrNe Xo c (fun _ _ y => y.IsAlg ∧ Good y)) {κ : c.F} (hκ : κ ≠ 0) :
    BddGood Xo c la κ 1 ↔ 0 ≤ vLa la κ := by
  constructor
  · intro h
    obtain ⟨T, io, e, ho, y, hy⟩ := hne la
    have h1 := h T io e ho y hy.1 hy.2
    rw [evI_one, mul_one] at h1
    exact (inV_io ho hκ).mp h1
  · intro h T io e ho y _ _
    rw [evI_one, mul_one]
    exact (inV_io ho hκ).mpr h

end GlobalTheory.GoodPtsModel
