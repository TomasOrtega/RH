import Mathlib
import Formalism.PeriodIntegrals.SupportParts

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def CokDetL : Prop := ∀ (R : Type) [CommRing R] (n : ℕ) (Z Z' : Matrix (Fin n) (Fin n) R),
  Z.det ∈ nonZeroDivisors R → Z'.det ∈ nonZeroDivisors R →
  Nonempty (((Fin n → R) ⧸ LinearMap.range Z.mulVecLin) ≃ₗ[R] ((Fin n → R) ⧸ LinearMap.range Z'.mulVecLin)) →
  ∃ u : Rˣ, Z'.det = u * Z.det

def DetForm : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (T T' : ℕ),
  ∃ C : Option D.host.E → (D.s.atP p).Ep, ∀ (w : Point D.host.E (D.R.rS + 1))
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)), modPt δ T T' p w = some a →
    a.mat.det = (D.s.atP p).ιE (Dmin w (D.R.rS + 1)) * C (kind w)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem uLow_det {E : Type} [CommRing E] {n : ℕ} (x : Loc.IL n → E) : (Loc.uLow x).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i j hij => ?_)]
  · simp [Loc.uLow]
  · have hij' : i < j := hij
    simp only [Loc.uLow]
    rw [if_neg (ne_of_lt hij'), dif_neg (not_lt.2 hij'.le)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem uUp_det {E : Type} [CommRing E] {n : ℕ} (w : Loc.Pt E n) (y : Loc.IN w → E) :
    (Loc.uUp w y).det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => ?_)]
  · simp [Loc.uUp]
  · have hij' : j < i := hij
    simp only [Loc.uUp]
    rw [if_neg (ne_of_gt hij'), dif_neg (fun h => absurd h.1 (not_lt.2 hij'.le))]

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bb_exists {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) {m : ℕ} (w : Loc.Pt E (m + 1)) (c : M.Cls m) (h : M.BB w c ≠ 0) :
    ∃ Z : M.Mat (m + 1), (Z.Z.map M.R.subtype).det = w.mat.det ∧
      Nonempty (M.Iso Z (Quotient.out c)) := by
  have hex : ∃ xy, M.bbIntegrand w c xy ≠ 0 := by
    by_contra hne
    push Not at hne
    apply h
    unfold Loc.Model.BB
    simp [hne]
  obtain ⟨⟨x, y⟩, hxy⟩ := hex
  unfold Loc.Model.bbIntegrand at hxy
  simp only at hxy
  split_ifs at hxy with hZ
  · have h1 := left_ne_zero_of_mul hxy
    have h2 := Nat.cast_ne_zero.mp h1
    unfold Loc.Model.nIso at h2
    refine ⟨_, ?_, (Nat.card_ne_zero.mp h2).1⟩
    show (Loc.uLow x * w.mat * Loc.uUp w y).det = _
    rw [Matrix.det_mul, Matrix.det_mul, uLow_det, uUp_det, one_mul, mul_one]
  · exact absurd rfl hxy

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem bbtop_ne {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {T T' : ℕ} {p : PlF D}
    {w : Point D.host.E (D.R.rS + 1)} {c : Option ((M p).Cls D.R.rS)}
    (h : BBtop M δ T T' p w c ≠ 0) :
    ∃ a cl, modPt δ T T' p w = some a ∧ c = some cl ∧ (M p).BB a cl ≠ 0 := by
  unfold BBtop at h
  rcases hm : modPt δ T T' p w with _ | a <;> rcases c with _ | cl
  · simp [hm] at h
  · simp [hm] at h
  · simp [hm] at h
  · simp only [hm] at h
    exact ⟨a, cl, rfl, rfl, right_ne_zero_of_mul h⟩

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem modK_unit_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (u : (M.R)ˣ) (x : E) : M.modK ((u : M.R) * x) = M.modK x := by
  have hu : (((u : M.R) : E)) * ((((u⁻¹ : (M.R)ˣ) : M.R) : E)) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  unfold Loc.Model.modK
  congr 2
  ext z
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨((u : M.R) : E) * y, M.R.mul_mem (u : M.R).2 hy, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(((u⁻¹ : (M.R)ˣ) : M.R) : E) * y, M.R.mul_mem (↑u⁻¹ : M.R).2 hy, ?_⟩
    linear_combination (x * y) * hu

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem nzd_of_unit {E : Type} [CommRing E] (S : Subring E) (x : S) (h : IsUnit (x : E)) :
    x ∈ nonZeroDivisors S := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have h1 : (x : E) * (y : E) = 0 := by rw [← Subring.coe_mul, hy, Subring.coe_zero]
    exact Subtype.ext (by simpa using h.mul_right_eq_zero.1 h1)
  · have h1 : (y : E) * (x : E) = 0 := by rw [← Subring.coe_mul, hy, Subring.coe_zero]
    exact Subtype.ext (by simpa using h.mul_left_eq_zero.1 h1)

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Split into cases according to the possible forms of the given data. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Replace the relevant objects with their definitions. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules.

Establish an intermediate fact. Replace the relevant objects with their definitions. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Establish an intermediate fact.

Replace the relevant objects with their definitions. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem locStep_of (hC : CokDetL) (hD : DetForm)
    (hT : ∀ (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1)), Dmin w (D.R.rS + 1) ≠ 0)
    (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)) (hk : kind w = kind w')
    (c : Option ((M p).Cls D.R.rS)) (hw : BBtop M δ T T' p w c ≠ 0) (hw' : BBtop M δ T T' p w' c ≠ 0) :
    (M p).modK ((D.s.atP p).ιE (Dmin w (D.R.rS + 1))) =
        (M p).modK ((D.s.atP p).ιE (Dmin w' (D.R.rS + 1))) ∧
      (M p).modK ((D.s.atP p).ιE (Dmin w D.R.rS)) = (M p).modK ((D.s.atP p).ιE (Dmin w' D.R.rS)) := by
  obtain ⟨a, cl, ha, hc, hb⟩ := bbtop_ne hw
  obtain ⟨a', cl', ha', hc', hb'⟩ := bbtop_ne hw'
  rw [hc] at hc'
  cases hc'
  obtain ⟨Z, hZ, ⟨φ⟩⟩ := bb_exists (M p) a cl hb
  obtain ⟨Z', hZ', ⟨φ'⟩⟩ := bb_exists (M p) a' cl hb'
  have hmap : ∀ Y : (M p).Mat (D.R.rS + 1), (Y.Z.map (M p).R.subtype).det = ((Y.Z.det : (M p).R) : _) :=
    fun Y => (RingHom.map_det (M p).R.subtype Y.Z).symm
  have hu1 : IsUnit (Z.Z.map (M p).R.subtype).det := Z.unit
  have hu2 : IsUnit (Z'.Z.map (M p).R.subtype).det := Z'.unit
  have n1 : Z.Z.det ∈ nonZeroDivisors (M p).R := nzd_of_unit _ _ (by rw [← hmap]; exact hu1)
  have n2 : Z'.Z.det ∈ nonZeroDivisors (M p).R := nzd_of_unit _ _ (by rw [← hmap]; exact hu2)
  obtain ⟨u, hu⟩ := hC (M p).R (D.R.rS + 1) Z.Z Z'.Z n1 n2 ⟨φ.1.trans φ'.1.symm⟩
  obtain ⟨C, hCf⟩ := hD D δ p T T'
  have d1 := hCf w a ha
  have d2 := hCf w' a' ha'
  rw [← hk] at d2

  have e : a'.mat.det = ((u : (M p).R) : (D.s.atP p).Ep) * a.mat.det := by
    rw [← hZ, ← hZ', hmap, hmap, hu, Subring.coe_mul]
  have hua : IsUnit a.mat.det := hZ ▸ hu1
  have hCu : IsUnit (C (kind w)) := by
    rw [d1] at hua
    exact isUnit_of_mul_isUnit_right hua
  have key : (D.s.atP p).ιE (Dmin w' (D.R.rS + 1)) =
      ((u : (M p).R) : (D.s.atP p).Ep) * (D.s.atP p).ιE (Dmin w (D.R.rS + 1)) := by
    rw [d1, d2, ← mul_assoc] at e
    exact hCu.mul_right_cancel e
  refine ⟨by rw [key, modK_unit_mul], ?_⟩
  rcases hcase : kind w with _ | ζ
  · have h0 : Dmin w D.R.rS = 0 := by
      unfold kind at hcase
      by_contra hne
      simp [hne] at hcase
    have hcase' : kind w' = none := hk ▸ hcase
    have h0' : Dmin w' D.R.rS = 0 := by
      unfold kind at hcase'
      by_contra hne
      simp [hne] at hcase'
    rw [h0, h0']
  · have hcase' : kind w' = some ζ := hk ▸ hcase
    have hr : Dmin w D.R.rS ≠ 0 := by
      unfold kind at hcase
      by_contra hne
      simp [hne] at hcase
    have hr' : Dmin w' D.R.rS ≠ 0 := by
      unfold kind at hcase'
      by_contra hne
      simp [hne] at hcase'
    have hz : zetaOf w = ζ := by
      unfold kind at hcase
      simpa [hr] using hcase
    have hz' : zetaOf w' = ζ := by
      unfold kind at hcase'
      simpa [hr'] using hcase'
    have e1 : Dmin w (D.R.rS + 1) = ζ * Dmin w D.R.rS := by
      rw [← hz, zetaOf, div_mul_cancel₀ _ hr]
    have e1' : Dmin w' (D.R.rS + 1) = ζ * Dmin w' D.R.rS := by
      rw [← hz', zetaOf, div_mul_cancel₀ _ hr']
    have hζ : ζ ≠ 0 := by
      intro h0
      apply hT D w
      rw [e1, h0, zero_mul]
    have hζu : IsUnit ((D.s.atP p).ιE ζ) := (isUnit_iff_ne_zero.mpr hζ).map (D.s.atP p).ιE
    have key' : (D.s.atP p).ιE (Dmin w' D.R.rS) =
        ((u : (M p).R) : (D.s.atP p).Ep) * (D.s.atP p).ιE (Dmin w D.R.rS) := by
      rw [e1, e1', map_mul, map_mul] at key
      apply hζu.mul_left_cancel
      rw [key]
      ring
    rw [key', modK_unit_mul]

end PI.SupportDatumW
