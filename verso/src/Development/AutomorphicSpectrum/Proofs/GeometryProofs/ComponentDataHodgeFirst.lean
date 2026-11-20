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
Unfold `IsMultiHomog at *`. Introduce `m hm k`. Take `⟨m1, h1, m2, h2, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul p q hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, hp m1 h1 k, hq m2 h2 k, Pi.add_apply]`.
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
Unfold `IsMultiHomog at *`. Introduce `m hm k`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hp m h k`. Conclude with `hq m h k`.
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
Unfold `IsMultiHomog`. Introduce `m hm k'`. Rewrite `hm` using `[MvPolynomial.support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Distinguish the cases in `hk : k' = k`.

Substitute `hk` using the available equality. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Finsupp.single_apply, Ne.symm hb]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Establish `hk' : k ≠ k'` using `Ne.symm hk`. Simplify using `[Finsupp.single_apply, hk, hk']`.
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
Establish `key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (MvPolynomial.X ⟨k, ch k⟩ : MvPolynomial ((k : K) × Jt k) ℤ)) (∑ k ∈ s, Pi.single k 1)`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Establish `h1 : IsMultiHomog (MvPolynomial.C (1 : ℤ) : MvPolynomial ((k : K) × Jt k) ℤ) 0` using `isMultiHomog_C_zero 1`. Simplify using `using h1`.

Introduce `a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Apply the tactic sequence `exact isMultiHomog_mul_geometry (isMultiHomog_X_geometry a (ch a)) ih`. Establish `h` using `key Finset.univ`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
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
Unfold `IsValueAt at *`. Take `⟨d, g, h, hg, hh, hy, hgs, hw, rfl⟩` from `h1`. Take `⟨d', g', h', hg', hh', hy', hgs', hw', rfl⟩` from `h2`. Apply the tactic sequence `refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add_geometry (isMultiHomog_mul_geometry hg hh') ?_, isMultiHomog_mul_geometry hh hh', ?_, ?_, ?_, ?_⟩`. Rewrite using `[add_comm d d']`.

Apply the tactic sequence `exact isMultiHomog_mul_geometry hg' hh`. Rewrite using `[map_mul]`. Conclude with `mul_ne_zero hy hy'`. Simplify using `only [map_mul, map_add, hgs, hgs']`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [map_mul]`. Conclude with `mul_ne_zero hw hw'`. Simplify using `only [map_mul, map_add]`. Rewrite using `[div_add_div _ _ hw hw']`. Expand and normalize the polynomial expressions, which then agree.
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
Unfold `IsValueAt at *`. Take `⟨d, g, h, hg, hh, hy, hgs, hw, rfl⟩` from `h1`. Take `⟨d', g', h', hg', hh', hy', hgs', hw', rfl⟩` from `h2`. Apply the tactic sequence `refine ⟨d + d', g * g', h * h', isMultiHomog_mul_geometry hg hg', isMultiHomog_mul_geometry hh hh', ?_, ?_, ?_, ?_⟩`. Rewrite using `[map_mul]`.

Conclude with `mul_ne_zero hy hy'`. Simplify using `only [map_mul, hgs, hgs']`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_mul]`. Conclude with `mul_ne_zero hw hw'`.

Simplify using `only [map_mul]`. Rewrite using `[div_mul_div_comm]`.
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
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Unfold `IsValueAt`. Use `⟨0, MvPolynomial.C a, 1, isMultiHomog_C_zero a, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : IsMultiHomog (MvPolynomial.C (1 : ℤ) : MvPolynomial ((k : K) × Jt k) ℤ) 0` using `isMultiHomog_C_zero 1`.

Simplify using `using h1`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Consider the case `add p q hp hq => simpa only [map_add] using isValueAt_add' hp hq`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, map_mul]`. Use `isValueAt_mul' hp ?_` and prove the remaining obligations. Unfold `IsValueAt`.

Use `⟨fun _ => 1, ∏ k, MvPolynomial.X ⟨k, i k⟩, ∏ k, MvPolynomial.X ⟨k, ch k⟩, isMultiHomog_prod_X_one i, isMultiHomog_prod_X_one ch, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify `hy` using `[segreCoord]`. Simplify using `only [map_prod, MvPolynomial.aeval_X]`. Conclude with `(div_mul_cancel₀ _ hy).symm`. Simplify using `using hw`.

Simplify using `[MvPolynomial.aeval_X]`.
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
Introduce `E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w hco`. Unfold `CoordsAt at hco`. Use `choose ch hch using hco.1`. Establish `hy : ∀ k, Dc.y ⟨k, ch k⟩ ≠ 0` using `fun k => (hco.2 k (ch k) (hch k)).1`. Establish `hwc : ∀ k, w ⟨k, ch k⟩ ≠ 0` using `fun k => (hch k).ne_zero`.

Establish `hseg : segreCoord Dc.y ch ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun k _ => hy k)`. Establish `hsegw : ∏ k, w ⟨k, ch k⟩ ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun k _ => hwc k)`. Take `⟨m, f, cc, hf, hcc, hsum, hfr⟩` from `Hd.locally ch hseg`. Establish `hmem : ∀ a, a ∈ chartRing ℤ (segreCoord Dc.y) ch → ∃ P : MvPolynomial ((k : K) → J k) ℤ, MvPolynomial.aeval (fun c' => segreCoord Dc.y c' / segreCoord Dc.y ch) P = a`. Introduce `a ha`.

Unfold `ReciprocityTheory.ChartRestriction.G.Geo.chartRing at ha`. Rewrite `ha` using `[Algebra.adjoin_range_eq_range_aeval]`. Take `⟨P, hP⟩` from `ha`. Conclude with `⟨P, hP⟩`. Use `choose P hP using fun l => hmem (f l) (hf l)`.

Use `choose Q hQ using fun l => hmem (cc l) (hcc l)`. Establish `hginj : Function.Injective (genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩)` using `(CoordTie.gen Or.𝔐.tie).inj _`. Establish `hlift : ∀ q : (k : K) × J k, ∃ t : Or.𝔐.X.presheaf.stalk (centre z), genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ t = Dc.y q / Dc.y ⟨q.1, ch q.1⟩ ∧ (Scheme.stalkClosedPointTo z).hom t = w q / w ⟨q.1, ch q.1⟩`. Introduce and unpack `⟨k, i⟩`. Take `⟨r0, hv, hr0⟩` from `(hco.2 k (ch k) (hch k)).2 i`.

Unfold `ValAt at hv`. Take `⟨hsp, t, ht1, ht2⟩` from `hv`. Use `⟨t, ht1, ?_⟩` and prove the remaining obligations. Rewrite using `[ht2, hr0, mul_div_assoc, div_self (hwc k), _root_.mul_one]`. Use `choose t ht1 ht2 using hlift`.

Take `⟨ψ, hψ⟩ : ∃ ψ : Or.𝔐.X.presheaf.stalk (centre z) →+* ℂ, ψ = (Scheme.stalkClosedPointTo z).hom` from `⟨_, rfl⟩`. Establish `ht2' : ∀ q, ψ (t q) = w q / w ⟨q.1, ch q.1⟩`. Introduce `q`. Rewrite using `[hψ]`. Conclude with `ht2 q`.

Establish `hval : ∀ R : MvPolynomial ((k : K) → J k) ℤ, ∃ s : Or.𝔐.X.presheaf.stalk (centre z), genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ s = MvPolynomial.aeval (fun c' => segreCoord Dc.y c' / segreCoord Dc.y ch) R ∧ ψ s = MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) R`. Introduce `R`. Proceed by induction on `R using MvPolynomial.induction_on with`. Consider the case `C a`. Use `⟨((a : ℤ) : Or.𝔐.X.presheaf.stalk (centre z)), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_intCast, MvPolynomial.aeval_C]`. Conclude with `(eq_intCast _ a).symm`. Rewrite using `[map_intCast, MvPolynomial.aeval_C]`. Conclude with `(eq_intCast _ a).symm`. Consider the case `add p q hp hq`.

Take `⟨s, hs1, hs2⟩` from `hp`. Take `⟨s', hs1', hs2'⟩` from `hq`. Conclude with `⟨s + s', by rw [map_add, map_add, hs1, hs1'], by rw [map_add, map_add, hs2, hs2']⟩`. Consider the case `mul_X p i hp`. Take `⟨s, hs1, hs2⟩` from `hp`.

Use `⟨s * ∏ k, t ⟨k, i k⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_prod, hs1, map_mul, MvPolynomial.aeval_X]`. Use `congr 1`. Simplify using `only [ht1]`. Unfold `segreCoord`.

Rewrite using `[Finset.prod_div_distrib]`. Rewrite using `[map_mul, map_prod, hs2, map_mul, MvPolynomial.aeval_X]`. Use `congr 1`. Simplify using `only [ht2']`. Rewrite using `[Finset.prod_div_distrib]`.

Take `⟨s, hs1, hs2⟩` from `hval (∑ l, Q l * P l - 1)`. Establish `hz : genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ s = 0`. Rewrite using `[hs1, map_sub, map_sum, map_one]`. Simplify using `only [map_mul, hP, hQ]`. Rewrite using `[hsum, sub_self]`.

Establish `hs0 : s = 0` using `hginj (by rw [hz, map_zero])`. Establish `hW : ∑ l, MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (Q l) * MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (P l) = 1`. Establish `h2` using `hs2`. Rewrite `h2` using `[hs0, map_zero, map_sub, map_sum, map_one]`. Simplify using `only [map_mul] at h2`.

Conclude with `sub_eq_zero.mp h2.symm`. Choose the witnesses or unpack the hypotheses as in `⟨l0, hl0⟩ : ∃ l, MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (P l) ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Rewrite `hW` using `[Finset.sum_eq_zero (fun l _ => by rw [hne l, MulZeroClass.mul_zero])]`.

Conclude with `zero_ne_one hW`. Establish `hunit : IsUnitAt Dc.y (f l0) w`. Establish `hv` using `isValueAt_aeval_segreCoord_div Dc.y w ch hseg hsegw (P l0)`. Rewrite `hv` using `[hP l0]`. Conclude with `Exists.intro _ (And.intro hv hl0)`.

Take `⟨b, hb, u, hu, hΛ⟩` from `hfr l0`. Conclude with `⟨MuFrameAt.mk ch (f l0) (And.intro hwc hunit) b hb u hu hΛ⟩`.
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
