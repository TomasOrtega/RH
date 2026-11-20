import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MemMCoordIdealIff
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveRingFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotLocal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointResidue
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.SectionBounded

noncomputable section

open CurveVerticalPointSurjective in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y s d hP hs hsP m hm hlen`. Establish `hfin` using `hFin K ι Ω y hP`. Take `⟨c, hyc, hrat⟩` from `hC K ι Ω y hP m hm`. Establish `hrat'` using `hrat`. Establish `: m.IsPrime` using `hm.isPrime`.

Establish `hYne : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0` using `fun e => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)`. Establish `hunit : ∀ b : m.primeCompl, IsUnit ((curveRing y).subtype (b : curveRing y))`. Introduce `b`. Use `isUnit_iff_ne_zero.mpr fun h => b.2 ?_` and prove the remaining obligations. Establish `hb0 : (b : curveRing y) = 0` using `Subtype.ext h`.

Rewrite using `[hb0]`. Conclude with `m.zero_mem`. Set `L` to `Localization.AtPrime m`. Set `φ : L →+* Ω` to `IsLocalization.lift hunit`. Establish `hinj0 : Function.Injective (algebraMap (curveRing y) L)` using `IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors m)`.

Establish `hφinj : Function.Injective φ` using `(IsLocalization.lift_injective_iff hunit).mpr fun x x' => ⟨fun h => by rw [hinj0 h], fun h => by rw [Subtype.val_injective h]⟩`. Establish `hφB : ∀ x : curveRing y, φ (algebraMap _ L x) = x` using `fun x => IsLocalization.lift_eq hunit x`. Establish `hφmk : ∀ (a : curveRing y) (b : m.primeCompl) (v : Ω), φ (IsLocalization.mk' L a b) = v ↔ (a : Ω) = ((b : curveRing y) : Ω) * v` using `fun a b v => IsLocalization.lift_mk'_spec hunit a v b`. Use `choose α β hβ hαβ using hrat`. Set `ρ : (Σ k, ι k) → L` to `fun p => IsLocalization.mk' L (α p) (⟨β p, hβ p⟩ : m.primeCompl)`.

Establish `hφρ : ∀ p, φ (ρ p) = y p / y ⟨p.1, c p.1⟩` using `fun p => (hφmk _ _ _).mpr (hαβ p).symm`. Establish `hφev : ∀ {g : MRing ι} {e : K → ℕ}, IsMultiHomog g e → φ (aeval ρ g) = aeval y g * (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹`. Introduce `g e hg`. Rewrite using `[ringHom_aeval φ ρ g, show (fun p => φ (ρ p)) = fun p => y p / y ⟨p.1, c p.1⟩ from funext hφρ]`. Conclude with `CurveVerticalPointResidue.aeval_div y c g e hg`.

Establish `hevB : ∀ {g : MRing ι} {e : K → ℕ} (x : curveRing y), IsMultiHomog g e → aeval y g = (x : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → aeval ρ g = algebraMap _ L x`. Introduce `g e x hg hgx`. Apply `hφinj` to reduce the goal to its premises. Rewrite using `[hφev hg, hφB, hgx, mul_assoc, mul_inv_cancel₀ (hYne e), mul_one]`. Set `r : (Σ k, ι k) → IsLocalRing.ResidueField L` to `fun p => IsLocalRing.residue L (ρ p)`.

Establish `hWform : ∀ {g : MRing ι} {e : K → ℕ}, IsMultiHomog g e → (g ∈ mCoordIdeal r ↔ aeval ρ g ∈ IsLocalRing.maximalIdeal L)`. Introduce `g e hg`. Rewrite using `[mem_mCoordIdeal_iff r hg, ← IsLocalRing.residue_eq_zero_iff, ringHom_aeval]`. Establish `hWB : ∀ {g : MRing ι} {e : K → ℕ} (x : curveRing y), IsMultiHomog g e → aeval y g = (x : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → (g ∈ mCoordIdeal r ↔ x ∈ m)`. Introduce `g e x hg hgx`.

Rewrite using `[hWform hg, hevB x hg hgx]`. Conclude with `IsLocalization.AtPrime.to_map_mem_maximal_iff L m x`. Establish `hXc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal r`. Introduce `k`. Establish `hρ1 : ρ ⟨k, c k⟩ = 1` using `hφinj (by rw [hφρ, map_one, div_self (hyc k)])`.

Rewrite using `[hWform (homog_X ⟨k, c k⟩), aeval_X, hρ1]`. Conclude with `fun h => (IsLocalRing.maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).mpr h)`. Establish `hWprime : (mCoordIdeal r).IsPrime` using `RingHom.ker_isPrime _`. Establish `hPW : mCoordIdeal y ≤ mCoordIdeal r`. Take `⟨S, hS, hPS⟩` from `CoordinateConeArithVar.isMultiHomogIdeal y`.

Introduce `f hfP`. Rewrite `hfP` using `[hPS]`. Use `(Ideal.span_le.mpr ?_) hfP` and prove the remaining obligations. Introduce `f hf`. Take `⟨e, he⟩` from `hS f hf`.

Establish `hfP' : f ∈ mCoordIdeal y` using `by rw [hPS]; exact Ideal.subset_span hf`. Establish `hf0 : aeval y f = ((0 : curveRing y) : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k`. Rewrite using `[(mem_mCoordIdeal_iff y he).mp hfP']`. Simplify using the standard rewrite rules. Conclude with `(hWB 0 he hf0).mpr m.zero_mem`.

Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.mk'_surjective m.primeCompl (aeval ρ s)`. Simplify using `only at hab`. Establish `hbx : ((b : curveRing y) : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k`. Establish `h1` using `hφev hs`. Rewrite `h1` using `[← hab]`.

Rewrite using `[(hφmk a b _).mp h1, mul_assoc, inv_mul_cancel_right₀ (hYne d)]`. Establish `hlenA : locLen m (curveRing y ⧸ Ideal.span {a}) ≠ 0`. Rewrite using `[← CurveSectionQuotLocal.proof K ι Ω y s d hP hs hsP m c hm.isPrime hyc hrat' a b b.2 hbx]` and apply the resulting hypothesis. Establish `ham : a ∈ m`. Assume the negation of the conclusion as `h`.

Conclude with `hlenA (locLen_quot_eq_zero m h)`. Establish `hsW : s ∈ mCoordIdeal r`. Rewrite using `[hWform hs, ← hab]`. Conclude with `(IsLocalization.AtPrime.mk'_mem_maximal_iff L m a b).mpr ham`. Establish `hJW : mCoordIdeal y ⊔ Ideal.span {s} ≤ mCoordIdeal r` using `sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)`.

Establish `hcurve : curvePtIdeal y (mCoordIdeal r) = m`. Apply `le_antisymm` to reduce the goal to its premises. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `x ⟨e, g, h, hg, hh, hgW, hhW, hx⟩`. Establish `heq : algebraMap _ L x * aeval ρ h = aeval ρ g`.

Apply `hφinj` to reduce the goal to its premises. Rewrite using `[map_mul, hφB, hφev hh, hφev hg, ← hx]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : algebraMap _ L x * aeval ρ h ∈ IsLocalRing.maximalIdeal L`. Rewrite using `[heq]`.

Conclude with `(hWform hg).mp hgW`. Break down `(IsLocalRing.maximalIdeal.isMaximal L).isPrime.mem_or_mem hmem with h1 | h1` into its components or cases. Conclude with `(IsLocalization.AtPrime.to_map_mem_maximal_iff L m x).mp h1`. Conclude with `absurd ((hWform hh).mpr h1) hhW`. Introduce `x hx`.

Take `⟨e, g, hg, hgx⟩` from `exists_form y c hyc x`. Establish `hgW : g ∈ mCoordIdeal r` using `(hWB x hg hgx).mpr hx`. Establish `hXW : chartMon c e ∉ mCoordIdeal r` using `chartMon_notMem hWprime hXc e`. Establish `hval : (x : Ω) * aeval y (chartMon c e) = aeval y g`. Rewrite using `[aeval_chartMon, hgx]`.

Establish `key : x ∈ {b : curveRing y | ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ g ∈ mCoordIdeal r ∧ h ∉ mCoordIdeal r ∧ (b : Ω) * aeval y h = aeval y g}` using `⟨e, g, chartMon c e, hg, homog_chartMon c e, hgW, hXW, hval⟩`. Conclude with `Ideal.subset_span key`. Establish `ha0 : a ≠ 0`. Introduce `h0`. Establish `hx0 : aeval y s ≠ 0` using `fun h => hsP ((mem_mCoordIdeal_iff y hs).mpr h)`.

Establish `hb0 : ((b : curveRing y) : Ω) ≠ 0`. Introduce `h`. Apply `b.2` to reduce the goal to its premises. Rewrite using `[show (b : curveRing y) = 0 from Subtype.ext h]`. Conclude with `m.zero_mem`.

Establish `h2` using `hbx`. Rewrite `h2` using `[h0, ZeroMemClass.coe_zero, zero_mul]`. Conclude with `mul_ne_zero hb0 hx0 h2`. Establish `hWfrac : ∀ {f : MRing ι} {n : K → ℕ}, IsMultiHomog f n → f ∈ mCoordIdeal r → ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧ (b' : Ω) * aeval y f = (a' : Ω) * ∏ k, y ⟨k, c k⟩ ^ n k`. Introduce `f n hf hfW`.

Take `⟨⟨a', b'⟩, hab'⟩` from `IsLocalization.mk'_surjective m.primeCompl (aeval ρ f)`. Simplify using `only at hab'`. Use `⟨a', b', ?_, b'.2, ?_⟩` and prove the remaining obligations. Establish `h1` using `(hWform hf).mp hfW`. Rewrite `h1` using `[← hab']`.

Conclude with `(IsLocalization.AtPrime.mk'_mem_maximal_iff L m a' b').mp h1`. Establish `h1` using `hφev hf`. Rewrite `h1` using `[← hab']`. Rewrite using `[(hφmk a' b' _).mp h1, mul_assoc, inv_mul_cancel_right₀ (hYne n)]`. Establish `hmin : ∀ Q : Ideal (MRing ι), Q.IsPrime → mCoordIdeal y ⊔ Ideal.span {s} ≤ Q → Q ≤ mCoordIdeal r → mCoordIdeal r ≤ Q`.

Introduce `Q hQ hJQ hQW`. Establish `hPQ : mCoordIdeal y ≤ Q` using `le_trans le_sup_left hJQ`. Establish `hsQ : s ∈ Q` using `hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`. Conclude with `le_of_minimal y c hyc hfin m hm (mCoordIdeal r) Q hQ hPQ hQW hXc hWB hWfrac (CoordinateConeArithVar.isMultiHomogIdeal r) ha0 hs hsQ hbx`. Establish `hmp : mCoordIdeal r ∈ (mCoordIdeal y ⊔ Ideal.span {s}).minimalPrimes` using `⟨⟨hWprime, hJW⟩, fun Q hQ hQW => hmin Q hQ.1 hQ.2 hQW⟩`.

Conclude with `⟨mCoordIdeal r, ⟨hmp, fun k => ⟨c k, hXc k⟩⟩, hcurve⟩`.
-/
theorem CurveVertPointSurj.proof (hFin : CurveRingFinite.Statement) (hC : CurveClosedPointChart.Statement) :
    CurveVertPointSurj.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hP hs hsP m hm hlen
  have hfin := hFin K ι Ω y hP
  obtain ⟨c, hyc, hrat⟩ := hC K ι Ω y hP m hm
  have hrat' := hrat
  have : m.IsPrime := hm.isPrime
  have hYne : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)

  have hunit : ∀ b : m.primeCompl, IsUnit ((curveRing y).subtype (b : curveRing y)) := by
    intro b
    refine isUnit_iff_ne_zero.mpr fun h => b.2 ?_
    have hb0 : (b : curveRing y) = 0 := Subtype.ext h
    rw [hb0]
    exact m.zero_mem
  let L := Localization.AtPrime m
  let φ : L →+* Ω := IsLocalization.lift hunit
  have hinj0 : Function.Injective (algebraMap (curveRing y) L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors m)
  have hφinj : Function.Injective φ :=
    (IsLocalization.lift_injective_iff hunit).mpr fun x x' =>
      ⟨fun h => by rw [hinj0 h], fun h => by rw [Subtype.val_injective h]⟩
  have hφB : ∀ x : curveRing y, φ (algebraMap _ L x) = x := fun x => IsLocalization.lift_eq hunit x
  have hφmk : ∀ (a : curveRing y) (b : m.primeCompl) (v : Ω),
      φ (IsLocalization.mk' L a b) = v ↔ (a : Ω) = ((b : curveRing y) : Ω) * v :=
    fun a b v => IsLocalization.lift_mk'_spec hunit a v b

  choose α β hβ hαβ using hrat
  let ρ : (Σ k, ι k) → L := fun p => IsLocalization.mk' L (α p) (⟨β p, hβ p⟩ : m.primeCompl)
  have hφρ : ∀ p, φ (ρ p) = y p / y ⟨p.1, c p.1⟩ := fun p => (hφmk _ _ _).mpr (hαβ p).symm
  have hφev : ∀ {g : MRing ι} {e : K → ℕ}, IsMultiHomog g e →
      φ (aeval ρ g) = aeval y g * (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹ := by
    intro g e hg
    rw [ringHom_aeval φ ρ g, show (fun p => φ (ρ p)) = fun p => y p / y ⟨p.1, c p.1⟩ from funext hφρ]
    exact CurveVerticalPointResidue.aeval_div y c g e hg
  have hevB : ∀ {g : MRing ι} {e : K → ℕ} (x : curveRing y), IsMultiHomog g e →
      aeval y g = (x : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → aeval ρ g = algebraMap _ L x := by
    intro g e x hg hgx
    apply hφinj
    rw [hφev hg, hφB, hgx, mul_assoc, mul_inv_cancel₀ (hYne e), mul_one]

  let r : (Σ k, ι k) → IsLocalRing.ResidueField L := fun p => IsLocalRing.residue L (ρ p)
  have hWform : ∀ {g : MRing ι} {e : K → ℕ}, IsMultiHomog g e →
      (g ∈ mCoordIdeal r ↔ aeval ρ g ∈ IsLocalRing.maximalIdeal L) := by
    intro g e hg
    rw [mem_mCoordIdeal_iff r hg, ← IsLocalRing.residue_eq_zero_iff, ringHom_aeval]
  have hWB : ∀ {g : MRing ι} {e : K → ℕ} (x : curveRing y), IsMultiHomog g e →
      aeval y g = (x : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → (g ∈ mCoordIdeal r ↔ x ∈ m) := by
    intro g e x hg hgx
    rw [hWform hg, hevB x hg hgx]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff L m x
  have hXc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal r := by
    intro k
    have hρ1 : ρ ⟨k, c k⟩ = 1 := hφinj (by rw [hφρ, map_one, div_self (hyc k)])
    rw [hWform (homog_X ⟨k, c k⟩), aeval_X, hρ1]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hWprime : (mCoordIdeal r).IsPrime := RingHom.ker_isPrime _
  have hPW : mCoordIdeal y ≤ mCoordIdeal r := by
    obtain ⟨S, hS, hPS⟩ := CoordinateConeArithVar.isMultiHomogIdeal y
    intro f hfP
    rw [hPS] at hfP
    refine (Ideal.span_le.mpr ?_) hfP
    intro f hf
    obtain ⟨e, he⟩ := hS f hf
    have hfP' : f ∈ mCoordIdeal y := by rw [hPS]; exact Ideal.subset_span hf
    have hf0 : aeval y f = ((0 : curveRing y) : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k := by
      rw [(mem_mCoordIdeal_iff y he).mp hfP']
      simp
    exact (hWB 0 he hf0).mpr m.zero_mem

  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval ρ s)
  dsimp only at hab
  have hbx : ((b : curveRing y) : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k := by
    have h1 := hφev hs
    rw [← hab] at h1
    rw [(hφmk a b _).mp h1, mul_assoc, inv_mul_cancel_right₀ (hYne d)]
  have hlenA : locLen m (curveRing y ⧸ Ideal.span {a}) ≠ 0 := by
    rwa [← CurveSectionQuotLocal.proof K ι Ω y s d hP hs hsP m c hm.isPrime hyc hrat' a b b.2 hbx]
  have ham : a ∈ m := by
    by_contra h
    exact hlenA (locLen_quot_eq_zero m h)
  have hsW : s ∈ mCoordIdeal r := by
    rw [hWform hs, ← hab]
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff L m a b).mpr ham
  have hJW : mCoordIdeal y ⊔ Ideal.span {s} ≤ mCoordIdeal r :=
    sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)

  have hcurve : curvePtIdeal y (mCoordIdeal r) = m := by
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro x ⟨e, g, h, hg, hh, hgW, hhW, hx⟩
      have heq : algebraMap _ L x * aeval ρ h = aeval ρ g := by
        apply hφinj
        rw [map_mul, hφB, hφev hh, hφev hg, ← hx]
        ring
      have hmem : algebraMap _ L x * aeval ρ h ∈ IsLocalRing.maximalIdeal L := by
        rw [heq]
        exact (hWform hg).mp hgW
      rcases (IsLocalRing.maximalIdeal.isMaximal L).isPrime.mem_or_mem hmem with h1 | h1
      · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L m x).mp h1
      · exact absurd ((hWform hh).mpr h1) hhW
    · intro x hx
      obtain ⟨e, g, hg, hgx⟩ := exists_form y c hyc x
      have hgW : g ∈ mCoordIdeal r := (hWB x hg hgx).mpr hx
      have hXW : chartMon c e ∉ mCoordIdeal r := chartMon_notMem hWprime hXc e
      have hval : (x : Ω) * aeval y (chartMon c e) = aeval y g := by
        rw [aeval_chartMon, hgx]
      have key : x ∈ {b : curveRing y | ∃ (d : K → ℕ) (g h : MRing ι),
          IsMultiHomog g d ∧ IsMultiHomog h d ∧ g ∈ mCoordIdeal r ∧ h ∉ mCoordIdeal r ∧
            (b : Ω) * aeval y h = aeval y g} :=
        ⟨e, g, chartMon c e, hg, homog_chartMon c e, hgW, hXW, hval⟩
      exact Ideal.subset_span key
  have ha0 : a ≠ 0 := by
    intro h0
    have hx0 : aeval y s ≠ 0 := fun h => hsP ((mem_mCoordIdeal_iff y hs).mpr h)
    have hb0 : ((b : curveRing y) : Ω) ≠ 0 := by
      intro h
      apply b.2
      rw [show (b : curveRing y) = 0 from Subtype.ext h]
      exact m.zero_mem
    have h2 := hbx
    rw [h0, ZeroMemClass.coe_zero, zero_mul] at h2
    exact mul_ne_zero hb0 hx0 h2
  have hWfrac : ∀ {f : MRing ι} {n : K → ℕ}, IsMultiHomog f n → f ∈ mCoordIdeal r →
      ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧
        (b' : Ω) * aeval y f = (a' : Ω) * ∏ k, y ⟨k, c k⟩ ^ n k := by
    intro f n hf hfW
    obtain ⟨⟨a', b'⟩, hab'⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval ρ f)
    dsimp only at hab'
    refine ⟨a', b', ?_, b'.2, ?_⟩
    · have h1 := (hWform hf).mp hfW
      rw [← hab'] at h1
      exact (IsLocalization.AtPrime.mk'_mem_maximal_iff L m a' b').mp h1
    · have h1 := hφev hf
      rw [← hab'] at h1
      rw [(hφmk a' b' _).mp h1, mul_assoc, inv_mul_cancel_right₀ (hYne n)]

  have hmin : ∀ Q : Ideal (MRing ι), Q.IsPrime → mCoordIdeal y ⊔ Ideal.span {s} ≤ Q →
      Q ≤ mCoordIdeal r → mCoordIdeal r ≤ Q := by
    intro Q hQ hJQ hQW
    have hPQ : mCoordIdeal y ≤ Q := le_trans le_sup_left hJQ
    have hsQ : s ∈ Q := hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    exact le_of_minimal y c hyc hfin m hm (mCoordIdeal r) Q hQ hPQ hQW hXc hWB hWfrac
      (CoordinateConeArithVar.isMultiHomogIdeal r) ha0 hs hsQ hbx
  have hmp : mCoordIdeal r ∈ (mCoordIdeal y ⊔ Ideal.span {s}).minimalPrimes :=
    ⟨⟨hWprime, hJW⟩, fun Q hQ hQW => hmin Q hQ.1 hQ.2 hQW⟩
  exact ⟨mCoordIdeal r, ⟨hmp, fun k => ⟨c k, hXc k⟩⟩, hcurve⟩

end

end GroundTheory.Heights₂.Heights.Targets
