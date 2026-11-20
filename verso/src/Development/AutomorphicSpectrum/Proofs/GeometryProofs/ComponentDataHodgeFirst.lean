import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.MuFrame

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.
-/
private theorem isMultiHomog_mul_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {p q : MvPolynomial ((k : K) × Jt k) ℤ} {a b : K → ℕ}
    (hp : IsMultiHomog p a) (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  unfold IsMultiHomog at *
  intro m hm k
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hp m1 h1 k, hq m2 h2 k, Pi.add_apply]

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
private theorem isMultiHomog_add_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {p q : MvPolynomial ((k : K) × Jt k) ℤ} {a : K → ℕ}
    (hp : IsMultiHomog p a) (hq : IsMultiHomog q a) : IsMultiHomog (p + q) a := by
  classical
  unfold IsMultiHomog at *
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hp m h k
  · exact hq m h k

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem isMultiHomog_X_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] [DecidableEq K]
    (k : K) (i : Jt k) :
    IsMultiHomog (MvPolynomial.X ⟨k, i⟩ : MvPolynomial ((k : K) × Jt k) ℤ) (Pi.single k 1) := by
  classical
  unfold IsMultiHomog
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k' = k
  · subst hk
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · have hk' : k ≠ k' := Ne.symm hk
    simp [Finsupp.single_apply, hk, hk']

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem isMultiHomog_prod_X_one {K : Type} [Fintype K] {Jt : K → Type} [∀ k, Fintype (Jt k)]
    (ch : (k : K) → Jt k) :
    IsMultiHomog (∏ k, (MvPolynomial.X ⟨k, ch k⟩ : MvPolynomial ((k : K) × Jt k) ℤ)) (fun _ => 1) := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog
      (∏ k ∈ s, (MvPolynomial.X ⟨k, ch k⟩ : MvPolynomial ((k : K) × Jt k) ℤ))
      (∑ k ∈ s, Pi.single k 1) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h1 : IsMultiHomog (MvPolynomial.C (1 : ℤ) : MvPolynomial ((k : K) × Jt k) ℤ) 0 :=
        isMultiHomog_C_zero 1
      simpa using h1
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact isMultiHomog_mul_geometry (isMultiHomog_X_geometry a (ch a)) ih
  have h := key Finset.univ
  convert h using 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
private theorem isValueAt_add' {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] {Ω : Type} [Field Ω]
    {y : (k : K) × Jt k → Ω} {w : (k : K) × Jt k → ℂ} {s s' : Ω} {v v' : ℂ}
    (h1 : IsValueAt y s w v) (h2 : IsValueAt y s' w v') : IsValueAt y (s + s') w (v + v') := by
  unfold IsValueAt at *
  obtain ⟨d, g, h, hg, hh, hy, hgs, hw, rfl⟩ := h1
  obtain ⟨d', g', h', hg', hh', hy', hgs', hw', rfl⟩ := h2
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add_geometry (isMultiHomog_mul_geometry hg hh') ?_,
    isMultiHomog_mul_geometry hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']; exact isMultiHomog_mul_geometry hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_mul, map_add, hgs, hgs']; ring
  · simp only [map_mul]; exact mul_ne_zero hw hw'
  · simp only [map_mul, map_add]; rw [div_add_div _ _ hw hw']; ring

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem isValueAt_mul' {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] {Ω : Type} [Field Ω]
    {y : (k : K) × Jt k → Ω} {w : (k : K) × Jt k → ℂ} {s s' : Ω} {v v' : ℂ}
    (h1 : IsValueAt y s w v) (h2 : IsValueAt y s' w v') : IsValueAt y (s * s') w (v * v') := by
  unfold IsValueAt at *
  obtain ⟨d, g, h, hg, hh, hy, hgs, hw, rfl⟩ := h1
  obtain ⟨d', g', h', hg', hh', hy', hgs', hw', rfl⟩ := h2
  refine ⟨d + d', g * g', h * h', isMultiHomog_mul_geometry hg hg', isMultiHomog_mul_geometry hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_mul, hgs, hgs']; ring
  · simp only [map_mul]; exact mul_ne_zero hw hw'
  · simp only [map_mul]; rw [div_mul_div_comm]

/- English proof (translation)
Proceed by induction. Treat this case separately. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private theorem isValueAt_aeval_segreCoord_div {K : Type} [Fintype K] {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {Ω : Type} [Field Ω] (y : (k : K) × Jt k → Ω) (w : (k : K) × Jt k → ℂ) (ch : (k : K) → Jt k)
    (hy : segreCoord y ch ≠ 0) (hw : ∏ k, w ⟨k, ch k⟩ ≠ 0) (P : MvPolynomial ((k : K) → Jt k) ℤ) :
    IsValueAt y (MvPolynomial.aeval (fun c' => segreCoord y c' / segreCoord y ch) P) w
      (MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    unfold IsValueAt
    refine ⟨0, MvPolynomial.C a, 1, isMultiHomog_C_zero a, ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : IsMultiHomog (MvPolynomial.C (1 : ℤ) : MvPolynomial ((k : K) × Jt k) ℤ) 0 :=
        isMultiHomog_C_zero 1
      simpa using h1
    · simp
    · simp
    · simp
    · simp
  | add p q hp hq => simpa only [map_add] using isValueAt_add' hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    refine isValueAt_mul' hp ?_
    unfold IsValueAt
    refine ⟨fun _ => 1, ∏ k, MvPolynomial.X ⟨k, i k⟩, ∏ k, MvPolynomial.X ⟨k, ch k⟩,
      isMultiHomog_prod_X_one i, isMultiHomog_prod_X_one ch, ?_, ?_, ?_, ?_⟩
    · simpa [segreCoord] using hy
    · simp only [map_prod, MvPolynomial.aeval_X]
      exact (div_mul_cancel₀ _ hy).symm
    · simpa using hw
    · simp [MvPolynomial.aeval_X]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem nonempty_muFrameAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) := by
  classical
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w hco
  unfold CoordsAt at hco
  choose ch hch using hco.1
  have hy : ∀ k, Dc.y ⟨k, ch k⟩ ≠ 0 := fun k => (hco.2 k (ch k) (hch k)).1
  have hwc : ∀ k, w ⟨k, ch k⟩ ≠ 0 := fun k => (hch k).ne_zero
  have hseg : segreCoord Dc.y ch ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hy k)
  have hsegw : ∏ k, w ⟨k, ch k⟩ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hwc k)
  obtain ⟨m, f, cc, hf, hcc, hsum, hfr⟩ := Hd.locally ch hseg
  have hmem : ∀ a, a ∈ chartRing ℤ (segreCoord Dc.y) ch → ∃ P : MvPolynomial ((k : K) → J k) ℤ,
      MvPolynomial.aeval (fun c' => segreCoord Dc.y c' / segreCoord Dc.y ch) P = a := by
    intro a ha
    unfold ReciprocityTheory.ChartRestriction.G.Geo.chartRing at ha
    rw [Algebra.adjoin_range_eq_range_aeval] at ha
    obtain ⟨P, hP⟩ := ha
    exact ⟨P, hP⟩
  choose P hP using fun l => hmem (f l) (hf l)
  choose Q hQ using fun l => hmem (cc l) (hcc l)
  have hginj : Function.Injective (genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩) :=
    (CoordTie.gen Or.𝔐.tie).inj _
  have hlift : ∀ q : (k : K) × J k, ∃ t : Or.𝔐.X.presheaf.stalk (centre z),
      genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ t = Dc.y q / Dc.y ⟨q.1, ch q.1⟩ ∧
      (Scheme.stalkClosedPointTo z).hom t = w q / w ⟨q.1, ch q.1⟩ := by
    rintro ⟨k, i⟩
    obtain ⟨r0, hv, hr0⟩ := (hco.2 k (ch k) (hch k)).2 i
    unfold ValAt at hv
    obtain ⟨hsp, t, ht1, ht2⟩ := hv
    refine ⟨t, ht1, ?_⟩
    rw [ht2, hr0, mul_div_assoc, div_self (hwc k), _root_.mul_one]
  choose t ht1 ht2 using hlift
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Or.𝔐.X.presheaf.stalk (centre z) →+* ℂ,
      ψ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have ht2' : ∀ q, ψ (t q) = w q / w ⟨q.1, ch q.1⟩ := by
    intro q; rw [hψ]; exact ht2 q
  have hval : ∀ R : MvPolynomial ((k : K) → J k) ℤ, ∃ s : Or.𝔐.X.presheaf.stalk (centre z),
      genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ s =
        MvPolynomial.aeval (fun c' => segreCoord Dc.y c' / segreCoord Dc.y ch) R ∧
      ψ s =
        MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) R := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a =>
      refine ⟨((a : ℤ) : Or.𝔐.X.presheaf.stalk (centre z)), ?_, ?_⟩
      · rw [map_intCast, MvPolynomial.aeval_C]; exact (eq_intCast _ a).symm
      · rw [map_intCast, MvPolynomial.aeval_C]; exact (eq_intCast _ a).symm
    | add p q hp hq =>
      obtain ⟨s, hs1, hs2⟩ := hp
      obtain ⟨s', hs1', hs2'⟩ := hq
      exact ⟨s + s', by rw [map_add, map_add, hs1, hs1'], by rw [map_add, map_add, hs2, hs2']⟩
    | mul_X p i hp =>
      obtain ⟨s, hs1, hs2⟩ := hp
      refine ⟨s * ∏ k, t ⟨k, i k⟩, ?_, ?_⟩
      · rw [map_mul, map_prod, hs1, map_mul, MvPolynomial.aeval_X]
        congr 1
        simp only [ht1]
        unfold segreCoord
        rw [Finset.prod_div_distrib]
      · rw [map_mul, map_prod, hs2, map_mul, MvPolynomial.aeval_X]
        congr 1
        simp only [ht2']
        rw [Finset.prod_div_distrib]
  obtain ⟨s, hs1, hs2⟩ := hval (∑ l, Q l * P l - 1)
  have hz : genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ s = 0 := by
    rw [hs1, map_sub, map_sum, map_one]
    simp only [map_mul, hP, hQ]
    rw [hsum, sub_self]
  have hs0 : s = 0 := hginj (by rw [hz, map_zero])
  have hW : ∑ l, MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (Q l) *
      MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (P l) = 1 := by
    have h2 := hs2
    rw [hs0, map_zero, map_sub, map_sum, map_one] at h2
    simp only [map_mul] at h2
    exact sub_eq_zero.mp h2.symm
  obtain ⟨l0, hl0⟩ : ∃ l, MvPolynomial.aeval
      (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (P l) ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero (fun l _ => by rw [hne l, MulZeroClass.mul_zero])] at hW
    exact zero_ne_one hW
  have hunit : IsUnitAt Dc.y (f l0) w := by
    have hv := isValueAt_aeval_segreCoord_div Dc.y w ch hseg hsegw (P l0)
    rw [hP l0] at hv
    exact Exists.intro _ (And.intro hv hl0)
  obtain ⟨b, hb, u, hu, hΛ⟩ := hfr l0
  exact ⟨MuFrameAt.mk ch (f l0) (And.intro hwc hunit) b hb u hu hΛ⟩

end GlobalTheory.CompanionTheory.Ar.MuFrame
