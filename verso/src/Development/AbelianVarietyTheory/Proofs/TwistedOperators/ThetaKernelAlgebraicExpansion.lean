import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.AlgWave

open GlobalTheory.PlaceModel

abbrev Qb : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

variable {G : Type} [AddCommGroup G]

def algSpan (χ : G → G → ℂ) (X Y L : AddSubgroup G) : Submodule Qb (G → ℂ) :=
  Submodule.span Qb {Φ | ∃ x ∈ X, ∃ y ∈ Y, Φ = wave χ L x y}

/- English proof (translation)
The claim follows from `M.smul_mem (⟨a, ha⟩ : Qb) hΦ`.
-/
theorem smul_mem_of_mem {M : Submodule Qb (G → ℂ)} {a : ℂ} (ha : a ∈ Qb) {Φ : G → ℂ} (hΦ : Φ ∈ M) : a • Φ ∈ M :=
  M.smul_mem (⟨a, ha⟩ : Qb) hΦ

variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨x, hx, y, hy, rfl⟩`.
-/
theorem wave_mem {x y : G} (hx : x ∈ X) (hy : y ∈ Y) : wave χ L x y ∈ algSpan χ X Y L :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem _ h`. Take `⟨a, ha, b, hb, rfl⟩` from `h`. Rewrite using `[wave_trans]`. Conclude with `wave_mem (add_mem hx ha) hb`.

Consider the case `zero => exact zero_mem _`. Consider the case `add f g _ _ hf hg => exact add_mem hf hg`. Consider the case `smul c f _ hf => exact Submodule.smul_mem _ c hf`.
-/
theorem trans_mem {Φ : G → ℂ} (hΦ : Φ ∈ algSpan χ X Y L) {x : G} (hx : x ∈ X) :
    (fun t => Φ (t + x)) ∈ algSpan χ X Y L := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [wave_trans]
    exact wave_mem (add_mem hx ha) hb
  | zero => exact zero_mem _
  | add f g _ _ hf hg => exact add_mem hf hg
  | smul c f _ hf => exact Submodule.smul_mem _ c hf

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem _ hh`. Take `⟨a, ha, b, hb, rfl⟩` from `hh`. Rewrite using `[wave_modul h]`. Conclude with `smul_mem_of_mem (hχ _ (neg_mem ha) _ hy) (wave_mem ha (add_mem hy hb))`.

Consider the case `zero => convert (algSpan χ X Y L).zero_mem using 1`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Consider the case `add f g _ _ hf hg => convert add_mem hf hg using 1`. Use function extensionality and compare the values at `t`.

Simplify using `[mul_add]`. Consider the case `smul c f _ hf`. Use `Submodule.smul_mem _ c hf using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Use `show χ t y * ((c : ℂ) * f t) = (c : ℂ) * (χ t y * f t)`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem modul_mem (h : IsBichar χ) (hχ : ∀ x ∈ X, ∀ y ∈ Y, χ x y ∈ Qb) {Φ : G → ℂ} (hΦ : Φ ∈ algSpan χ X Y L) {y : G}
    (hy : y ∈ Y) : (fun t => χ t y * Φ t) ∈ algSpan χ X Y L := by
  induction hΦ using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hh
    rw [wave_modul h]
    exact smul_mem_of_mem (hχ _ (neg_mem ha) _ hy) (wave_mem ha (add_mem hy hb))
  | zero => convert (algSpan χ X Y L).zero_mem using 1; funext t; simp
  | add f g _ _ hf hg => convert add_mem hf hg using 1; funext t; simp [mul_add]
  | smul c f _ hf =>
    convert Submodule.smul_mem _ c hf using 1
    funext t
    show χ t y * ((c : ℂ) * f t) = (c : ℂ) * (χ t y * f t)
    ring
end GlobalTheory.AlgWave

namespace GlobalTheory.AlgWave

open GlobalTheory.PlaceModel

variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}

/- English proof (translation)
Use `set K := L.map (nsmulAddMonoidHom k) with hK`. Establish `hKL : K ≤ L`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `nsmul_mem hu k`. Establish `key : ∀ R : Finset G, ∃ Φ ∈ algSpan χ X Y L, (∀ t ∈ K, Φ t = 1) ∧ (∀ t ∉ L, Φ t = 0) ∧ ∀ r ∈ R, r ∈ L → r ∉ K → ∀ u ∈ K, Φ (r + u) = 0`.

Introduce `R`. Proceed by induction on `R using Finset.induction_on with`. Consider the case `empty`. Use `⟨ind L, ?_, fun t ht => ?_, fun t ht => ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[← wave_zero h]`.

Conclude with `wave_mem (zero_mem _) (zero_mem _)`. Simplify using `[ind, hKL ht]`. Simplify using `[ind, ht]`. Consider the case `insert r R _ ih`. Take `⟨Φ, hΦ, h1, h2, h3⟩` from `ih`.

Distinguish the cases in `hr : r ∈ L ∧ r ∉ K`. Take `⟨r', hr', rfl⟩` from `dX r (hL hr.1)`. Establish `: ¬ ∀ y ∈ L', χ r' y = 1` using `fun hh => hr.2 ⟨r', hX r' hr' hh, rfl⟩`. Use `push_neg at this`. Take `⟨y, hy, hne⟩` from `this`.

Take `⟨y', hy', rfl⟩` from `dY y (hL' hy)`. Rewrite `hne` using `[← h.nsmul]`. Establish `hK1 : ∀ u ∈ K, χ u y' = 1`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `(h.nsmul k u y').trans (hLL' u hu _ hy)`.

Establish `hne' : χ (k • r') y' - 1 ≠ 0` using `sub_ne_zero.2 hne`. Establish `hq : χ (k • r') y' ∈ Qb` using `hχ _ (hL hr.1) _ hy'`. Use `⟨(χ (k • r') y' - 1)⁻¹ • (χ (k • r') y' • Φ - fun t => χ t y' * Φ t), smul_mem_of_mem (inv_mem (sub_mem hq (one_mem _))) (sub_mem (smul_mem_of_mem hq hΦ) (modul_mem h hχ hΦ hy')), fun t ht => ?_, fun t ht => ?_, fun s hs hsL hsK u hu => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, h1 t ht, hK1 t ht, mul_one]`. Conclude with `inv_mul_cancel₀ hne'`.

Simplify using `[h2 t ht]`. Break down `Finset.mem_insert.1 hs with rfl | hs` into its components or cases. Simplify using `[h.left, hK1 u hu]`. Simplify using `[h3 s hs hsL hsK u hu]`. Use `⟨Φ, hΦ, h1, h2, fun s hs hsL hsK u hu => ?_⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.1 hs with rfl | hs` into its components or cases. Conclude with `absurd ⟨hsL, hsK⟩ hr`. Conclude with `h3 s hs hsL hsK u hu`. Take `⟨Φ, hΦ, h1, h2, h3⟩` from `key hR.toFinset`. Use `hΦ using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `t`. Distinguish the cases in `ht : t ∈ K`. Simplify using `[ind, ht, h1 t ht]`. Rewrite using `[ind, if_neg ht]`. Distinguish the cases in `htL : t ∈ L`.

Take `⟨r, hr, u, hu, rfl⟩` from `hfin t htL`. Establish `huK : k • u ∈ K` using `⟨u, hu, rfl⟩`. Conclude with `(h3 r (hR.mem_toFinset.2 hr) ((add_mem_cancel_right (hKL huK)).1 htL) (fun hh => ht (add_mem hh huK)) _ huK).symm`. Conclude with `(h2 t htL).symm`.
-/
theorem ind_nsmul_mem (h : IsBichar χ) (hχ : ∀ x ∈ X, ∀ y ∈ Y, χ x y ∈ Qb) (hL : L ≤ X) (hL' : L' ≤ Y)
    (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1)
    (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L) {k : ℕ}
    (dX : ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (R : Set G) (hR : R.Finite) (hfin : ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u) :
    ind (L.map (nsmulAddMonoidHom k)) ∈ algSpan χ X Y L := by
  classical
  set K := L.map (nsmulAddMonoidHom k) with hK
  have hKL : K ≤ L := by
    rintro _ ⟨u, hu, rfl⟩
    exact nsmul_mem hu k
  have key : ∀ R : Finset G, ∃ Φ ∈ algSpan χ X Y L, (∀ t ∈ K, Φ t = 1) ∧ (∀ t ∉ L, Φ t = 0) ∧
      ∀ r ∈ R, r ∈ L → r ∉ K → ∀ u ∈ K, Φ (r + u) = 0 := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      refine ⟨ind L, ?_, fun t ht => ?_, fun t ht => ?_, by simp⟩
      · rw [← wave_zero h]; exact wave_mem (zero_mem _) (zero_mem _)
      · simp [ind, hKL ht]
      · simp [ind, ht]
    | insert r R _ ih =>
      obtain ⟨Φ, hΦ, h1, h2, h3⟩ := ih
      by_cases hr : r ∈ L ∧ r ∉ K
      · obtain ⟨r', hr', rfl⟩ := dX r (hL hr.1)
        have : ¬ ∀ y ∈ L', χ r' y = 1 := fun hh => hr.2 ⟨r', hX r' hr' hh, rfl⟩
        push_neg at this
        obtain ⟨y, hy, hne⟩ := this
        obtain ⟨y', hy', rfl⟩ := dY y (hL' hy)
        rw [← h.nsmul] at hne
        have hK1 : ∀ u ∈ K, χ u y' = 1 := by
          rintro _ ⟨u, hu, rfl⟩
          exact (h.nsmul k u y').trans (hLL' u hu _ hy)
        have hne' : χ (k • r') y' - 1 ≠ 0 := sub_ne_zero.2 hne
        have hq : χ (k • r') y' ∈ Qb := hχ _ (hL hr.1) _ hy'
        refine ⟨(χ (k • r') y' - 1)⁻¹ • (χ (k • r') y' • Φ - fun t => χ t y' * Φ t),
          smul_mem_of_mem (inv_mem (sub_mem hq (one_mem _)))
            (sub_mem (smul_mem_of_mem hq hΦ) (modul_mem h hχ hΦ hy')), fun t ht => ?_,
          fun t ht => ?_, fun s hs hsL hsK u hu => ?_⟩
        · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, h1 t ht, hK1 t ht, mul_one]
          exact inv_mul_cancel₀ hne'
        · simp [h2 t ht]
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · simp [h.left, hK1 u hu]
          · simp [h3 s hs hsL hsK u hu]
      · refine ⟨Φ, hΦ, h1, h2, fun s hs hsL hsK u hu => ?_⟩
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact absurd ⟨hsL, hsK⟩ hr
        · exact h3 s hs hsL hsK u hu
  obtain ⟨Φ, hΦ, h1, h2, h3⟩ := key hR.toFinset
  convert hΦ using 1
  funext t
  by_cases ht : t ∈ K
  · simp [ind, ht, h1 t ht]
  · rw [ind, if_neg ht]
    by_cases htL : t ∈ L
    · obtain ⟨r, hr, u, hu, rfl⟩ := hfin t htL
      have huK : k • u ∈ K := ⟨u, hu, rfl⟩
      exact (h3 r (hR.mem_toFinset.2 hr) ((add_mem_cancel_right (hKL huK)).1 htL)
        (fun hh => ht (add_mem hh huK)) _ huK).symm
    · exact (h2 t htL).symm

/- English proof (translation)
Proceed by induction on `P using Finset.induction_on with`. Consider the case `empty`. Introduce `Φ _ _ _ h3`. Use `(algSpan χ X Y L).zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`.

Assume the negation of the conclusion as `ht`. Simplify using `using h3 t ht`. Consider the case `insert s P _ ih`. Introduce `Φ h0 h1 h2 h3`. Distinguish the cases in `hs : Φ s = 0`.

Use `ih Φ h0 h1 h2 fun t ht => ?_` and prove the remaining obligations. Take `⟨s', hs', u, hu, rfl⟩` from `h3 t ht`. Break down `Finset.mem_insert.1 hs' with rfl | hs'` into its components or cases. Conclude with `absurd ((h2 u hu _).trans hs) ht`. Conclude with `⟨s', hs', u, hu, rfl⟩`.

Establish `hsX` using `h1 s hs`. Establish `hm` using `smul_mem_of_mem (h0 s) (trans_mem hK (neg_mem hsX))`. Establish `hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K`. Introduce `t ht`. Establish `hn : t + -s ∉ K` using `fun hh => ht (by`.

Use `h2 _ hh s` as an intermediate fact. Rewrite `this` using `[show s + (t + -s) = t by abel]`. Simplify using `[ind, hh, this])`. Conclude with `⟨by simpa [ind, hn] using ht, hn⟩`. Establish `h0' : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ∈ Qb` using `fun t => by`.

Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Use `sub_mem (h0 t) (mul_mem (h0 s) ?_)` and prove the remaining obligations. Unfold `ind`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`.

Use `ih (Φ - Φ s • fun t => ind K (t + -s)) h0' (fun t ht => h1 t (hval t ht).1) (fun u hu t => by` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.smul_apply, h2 u hu]`. Rewrite using `[add_right_comm, ind_add K _ hu]) fun t ht => by`. Take `⟨s', hs', u, hu, rfl⟩` from `h3 t (hval t ht).1`. Break down `Finset.mem_insert.1 hs' with rfl | hs'` into its components or cases.

Conclude with `absurd (by simpa using hu) (hval _ ht).2`. Conclude with `⟨s', hs', u, hu, rfl⟩`. Simplify using `using add_mem this hm`.
-/
theorem mem_of_finite_cosets {K : AddSubgroup G} (hK : ind K ∈ algSpan χ X Y L) (P : Finset G) :
    ∀ Φ : G → ℂ, (∀ t, Φ t ∈ Qb) → (∀ t, Φ t ≠ 0 → t ∈ X) → (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) →
      (∀ t, Φ t ≠ 0 → ∃ s ∈ P, ∃ u ∈ K, t = s + u) → Φ ∈ algSpan χ X Y L := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro Φ _ _ _ h3
    convert (algSpan χ X Y L).zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s P _ ih =>
    intro Φ h0 h1 h2 h3
    by_cases hs : Φ s = 0
    · refine ih Φ h0 h1 h2 fun t ht => ?_
      obtain ⟨s', hs', u, hu, rfl⟩ := h3 t ht
      rcases Finset.mem_insert.1 hs' with rfl | hs'
      · exact absurd ((h2 u hu _).trans hs) ht
      · exact ⟨s', hs', u, hu, rfl⟩
    · have hsX := h1 s hs
      have hm := smul_mem_of_mem (h0 s) (trans_mem hK (neg_mem hsX))
      have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
        intro t ht
        have hn : t + -s ∉ K := fun hh => ht (by
          have := h2 _ hh s
          rw [show s + (t + -s) = t by abel] at this
          simp [ind, hh, this])
        exact ⟨by simpa [ind, hn] using ht, hn⟩
      have h0' : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ∈ Qb := fun t => by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        refine sub_mem (h0 t) (mul_mem (h0 s) ?_)
        unfold ind
        split_ifs
        exacts [one_mem _, zero_mem _]
      have := ih (Φ - Φ s • fun t => ind K (t + -s)) h0' (fun t ht => h1 t (hval t ht).1) (fun u hu t => by
        simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
        rw [add_right_comm, ind_add K _ hu]) fun t ht => by
          obtain ⟨s', hs', u, hu, rfl⟩ := h3 t (hval t ht).1
          rcases Finset.mem_insert.1 hs' with rfl | hs'
          · exact absurd (by simpa using hu) (hval _ ht).2
          · exact ⟨s', hs', u, hu, rfl⟩
      simpa using add_mem this hm

/- English proof (translation)
Take `⟨R, hR, hR'⟩` from `hfin k hk`. Take `⟨R2, hR2, hR2'⟩` from `hfin (k * k) (Nat.mul_pos hk hk)`. Establish `hP : ((fun t : G => k • t) ⁻¹' R2).Finite` using `hR2.preimage (tf k hk).injOn`. Use `mem_of_finite_cosets (K := L.map (nsmulAddMonoidHom k)) (ind_nsmul_mem h hχ hL hL' hLL' hX (dX k hk) (dY k hk) R hR hR') hP.toFinset Φ h0 h1 ?_ fun t ht => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`.

Conclude with `h2 u hu`. Take `⟨r, hr, u, hu, e⟩` from `hR2' _ (h3 t ht)`. Use `⟨t - k • u, hP.mem_toFinset.2 ?_, k • u, ⟨u, hu, rfl⟩, by abel⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `k • (t - k • u) ∈ R2`. Rewrite using `[smul_sub, e, smul_smul, add_sub_cancel_right]` and apply the resulting hypothesis.
-/
theorem mem_algSpan (h : IsBichar χ) (hχ : ∀ x ∈ X, ∀ y ∈ Y, χ x y ∈ Qb)
    (hL : L ≤ X) (hL' : L' ≤ Y) (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L)
    (dX : ∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u)
    (Φ : G → ℂ) (h0 : ∀ t, Φ t ∈ Qb) (h1 : ∀ t, Φ t ≠ 0 → t ∈ X) (k : ℕ) (hk : 0 < k)
    (h2 : ∀ u ∈ L, ∀ t, Φ (t + k • u) = Φ t) (h3 : ∀ t, Φ t ≠ 0 → k • t ∈ L) : Φ ∈ algSpan χ X Y L := by
  obtain ⟨R, hR, hR'⟩ := hfin k hk
  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : G => k • t) ⁻¹' R2).Finite := hR2.preimage (tf k hk).injOn
  refine mem_of_finite_cosets (K := L.map (nsmulAddMonoidHom k))
    (ind_nsmul_mem h hχ hL hL' hLL' hX (dX k hk) (dY k hk) R hR hR') hP.toFinset Φ h0 h1 ?_ fun t ht => ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact h2 u hu
  · obtain ⟨r, hr, u, hu, e⟩ := hR2' _ (h3 t ht)
    refine ⟨t - k • u, hP.mem_toFinset.2 ?_, k • u, ⟨u, hu, rfl⟩, by abel⟩
    change k • (t - k • u) ∈ R2
    rwa [smul_sub, e, smul_smul, add_sub_cancel_right]

end GlobalTheory.AlgWave

namespace GlobalTheory.BotFourier

open GlobalTheory.PlaceModel GlobalTheory.AlgWave GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `: infPart D (x i j) = 0` using `congrFun (congrFun hx i) j`. Express the relevant statement in the definitionally equal form `infPart D (k • x i j) = 0`. Rewrite using `[nsmul_eq_mul, RingHom.map_mul, this, mul_zero]`.
-/
theorem nsmul_finite {S T : HSp D} {x : WO S T} (hx : x.map (infPart D) = 0) (k : ℕ) :
    (k • x).map (infPart D) = 0 := by
  refine Matrix.ext fun i j => ?_
  have : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  change infPart D (k • x i j) = 0
  rw [nsmul_eq_mul, RingHom.map_mul, this, mul_zero]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [h.zero_left]`. Consider the case `succ k ih => rw [succ_nsmul, h.left, ih, pow_succ]`.
-/
theorem bichar_pow_left {G : Type} [AddCommGroup G] {χ : G → G → ℂ} (h : IsBichar χ) (k : ℕ) (x y : G) :
    χ (k • x) y = χ x y ^ k := by
  induction k with
  | zero => simp [h.zero_left]
  | succ k ih => rw [succ_nsmul, h.left, ih, pow_succ]

/- English proof (translation)
Take `⟨k, hk, hkx⟩` from `GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 x hx`. Take `⟨k', hk', hky⟩` from `GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 y hy`. Establish `hd` using `((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1 _ (nsmul_finite hx k)).1 hkx _ hky`. Establish `hb` using `isBichar_symplO S T ψ`. Rewrite `hd` using `[bichar_pow_left hb, ← hb.nsmul, bichar_pow_left hb, ← pow_mul]`.

Use `mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := k' * k) (Nat.mul_pos hk' hk) ?_)` and prove the remaining obligations. Rewrite using `[hd]`. Conclude with `isAlgebraic_one`.
-/
theorem psi_mem {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {x y : WO S T} (hx : x.map (infPart D) = 0)
    (hy : y.map (infPart D) = 0) : ψ (symplO S T x y) ∈ Qb := by
  obtain ⟨k, hk, hkx⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 x hx
  obtain ⟨k', hk', hky⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 y hy
  have hd := ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1 _ (nsmul_finite hx k)).1 hkx _ hky
  have hb := isBichar_symplO S T ψ
  rw [bichar_pow_left hb, ← hb.nsmul, bichar_pow_left hb, ← pow_mul] at hd
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := k' * k) (Nat.mul_pos hk' hk) ?_)
  rw [hd]
  exact isAlgebraic_one

/- English proof (translation)
Establish `h2 : symplOH S T x y + symplOH S T x y = symplO S T x y`. Unfold `symplOH`. Rewrite using `[← add_mul, ← map_add]`. Evaluate the numerical expressions. Establish `hp : ψ (symplOH S T x y) ^ 2 = ψ (symplO S T x y)`.

Rewrite using `[sq, ← AddChar.map_add_eq_mul, h2]`. Conclude with `mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := 2) two_pos (hp ▸ mem_algebraicClosure_iff.1 (psi_mem hψ hS hT hx hy)))`.
-/
theorem psiH_mem {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {x y : WO S T} (hx : x.map (infPart D) = 0)
    (hy : y.map (infPart D) = 0) : ψ (symplOH S T x y) ∈ Qb := by
  have h2 : symplOH S T x y + symplOH S T x y = symplO S T x y := by
    unfold symplOH
    rw [← add_mul, ← map_add]
    norm_num
  have hp : ψ (symplOH S T x y) ^ 2 = ψ (symplO S T x y) := by
    rw [sq, ← AddChar.map_add_eq_mul, h2]
  exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := 2) two_pos
    (hp ▸ mem_algebraicClosure_iff.1 (psi_mem hψ hS hT hx hy)))

/- English proof (translation)
Take `⟨-, -, -, m, hm, hord⟩` from `GlobalTheory.CharFin.char_finUnit_finite_order D ν hν`. Unfold `stdFst`. Use `split_ifs with hc`. Unfold `unitChar split_ifs with hu`. Take `⟨h1, h2, h3⟩` from `hu.choose_spec`.

Establish `hN : IsIntM (topL A.rank (frMapO A WW βA βW x))` using `StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.isIntM_topL hc.2.1`. Establish `hdet : (topL A.rank (frMapO A WW βA βW x)).det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Set `B : Matrix (Fin A.rank) (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)` to `fun a b => ⟨_, hN a b⟩`. Establish `hB : topL A.rank (frMapO A WW βA βW x) = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix B` using `rfl`. Rewrite using `[hB, ← RingHom.map_det]`.

Conclude with `(B.det).2`. Establish `hE` using `StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he`. Establish `hfu : Formalism.L2.Pj.FinUnit hu.choose` using `⟨h1, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by`. Rewrite using `[h2]`. Conclude with `add_mem (sub_mem (one_mem _) hE) (mul_mem hE hdet)), GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h3⟩`.

Establish `hpow` using `hord _ hfu`. Use `mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := m) hm ?_)` and prove the remaining obligations. Establish `e1 : (((ν hu.choose)⁻¹ : Circle) : ℂ) ^ m = Circle.coeHom (((ν hu.choose) ^ m)⁻¹)`. Rewrite using `[← inv_pow, map_pow]`. Both sides reduce to the same expression.

Rewrite using `[e1, hpow, inv_one, map_one]`. Conclude with `isAlgebraic_one`. Conclude with `zero_mem _`. Conclude with `zero_mem _`.
-/
theorem stdFst_mem {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) (I : Ideal (𝓞 D.host.E)) (A WW : HSp D) (βA : GL (Fin A.rank) (Lev.EAf D))
    (βW : GL (Fin WW.rank) (Lev.EAf D)) (x : WO A WW) : stdFst ν e I A WW βA βW x ∈ Qb := by
  obtain ⟨-, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  unfold stdFst
  split_ifs with hc
  · unfold unitChar
    split_ifs with hu
    · obtain ⟨h1, h2, h3⟩ := hu.choose_spec
      have hN : IsIntM (topL A.rank (frMapO A WW βA βW x)) := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.isIntM_topL hc.2.1
      have hdet : (topL A.rank (frMapO A WW βA βW x)).det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
        let B : Matrix (Fin A.rank) (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun a b => ⟨_, hN a b⟩
        have hB : topL A.rank (frMapO A WW βA βW x) = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix B := rfl
        rw [hB, ← RingHom.map_det]
        exact (B.det).2
      have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
      have hfu : Formalism.L2.Pj.FinUnit hu.choose := ⟨h1, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by
        rw [h2]; exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hdet)), GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h3⟩
      have hpow := hord _ hfu
      refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := m) hm ?_)
      have e1 : (((ν hu.choose)⁻¹ : Circle) : ℂ) ^ m = Circle.coeHom (((ν hu.choose) ^ m)⁻¹) := by
        rw [← inv_pow, map_pow]; rfl
      rw [e1, hpow, inv_one, map_one]
      exact isAlgebraic_one
    · exact zero_mem _
  · exact zero_mem _

end GlobalTheory.BotFourier

namespace GlobalTheory.BotFourier

open GlobalTheory.PlaceModel GlobalTheory.AlgWave

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t`. Establish `hI` using `hX.is`. Establish `hψ : IsStdChar D W.ψ (-1)` using `hI.isVac.1`. Establish `hν` using `(hI.weil' t).hecT`. Establish `hSd : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ`.

Use `⟨hI.rigA.1.1, fun y => (hI.rigA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩` and prove the remaining obligations. Simplify using `[GlobalTheory.Grid.neg_gram, hc]`. Simplify using `[GlobalTheory.Grid.neg_gram] at hc ⊢`. Conclude with `neg_eq_iff_eq_neg.2 hc`. Establish `hWd : IsSelfDualC WW X.rW.Λ` using `hI.rigW.1`.

Establish `he` using `hI.idem t`. Establish `hee` using `GlobalTheory.PlaceDatum.idemSum_mul_self he`. Establish `hinf` using `GlobalTheory.PlaceDatum.infPart_idemSum he`. Establish `hinf'` using `GlobalTheory.PlaceDatum.infPart_cA hinf`. Use `set S := GlobalTheory.Grid.neg A with hSdef`.

Use `set e := X.e t with hedef`. Use `set Λ : AddSubgroup (WO S WW) := latO S WW X.rA.Λ X.rW.Λ fun _ => True with hΛ`. Take `⟨K, hK, hC⟩` from `GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := S) hSd.1 hWd.1 X.rA.β X.rW.β`. Establish `hSB` using `StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_isSB hν.1 he (GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t) A WW X.rA.β X.rW.β Λ (GlobalTheory.PlaceDatum.exists_den_frMapO (S := S) hSd.1.fg hWd.1.fg X.rA.β X.rW.β) ⟨K, hK, fun t ht => hC t (GlobalTheory.Pl …`. Take `⟨⟨Tm, hTm⟩, hall⟩` from `hI.fst t`.

Rewrite using `[hall Tm hTm]`. Establish `hdual` using `(GlobalTheory.LatVac.latO_selfDual_approx_sign D W.ψ S WW X.rA.Λ X.rW.Λ hψ hSd hWd).1`. Establish `hfin` using `GlobalTheory.LatFinMod.latO_finite_mod D S WW _ _ hSd.1.fg hWd.1.fg fun _ => True`. Establish `he' : cA D e * cA D e = cA D e` using `by rw [← RingHom.map_mul, hee]`. Establish `hsm : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ ⊓ half S WW a` using `fun a ha u hu => AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S WW _ _ _ a (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩`.

Establish `finX : ∀ x ∈ half S WW e, x.map (infPart D) = 0` using `fun x hx => GlobalTheory.PlaceDatum.infPart_of_half hinf ((isHalf_iff S WW).2 hx)`. Establish `finY : ∀ y ∈ half S WW (cA D e), y.map (infPart D) = 0` using `fun y hy => GlobalTheory.PlaceDatum.infPart_of_half hinf' ((isHalf_iff S WW).2 hy)`. Establish `tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S WW => k • t` using `fun k hk a b hab => by`. Rewrite using `[← inv_smul_nsmul S WW hk a, ← inv_smul_nsmul S WW hk b]`. Conclude with `congrArg _ hab`.

Establish `hb` using `isBichar_symplO S WW W.ψ`. Take `⟨h1, k, hk, h2, h3⟩` from `hSB`. Establish `hmem` using `mem_algSpan (χ := fun x y : WO S WW => W.ψ (symplO S WW x y)) (X := half S WW e) (Y := half S WW (cA D e)) (L := Λ ⊓ half S WW e) (L' := Λ ⊓ half S WW (cA D e)) hb (fun x hx y hy => psi_mem hψ hSd hWd (finX x hx) (finY y hy)) inf_le_right inf_le_right (fun u hu y hy => (hdual u ( …`. Use `h _ (hsm _ he' u hu)` as an intermediate fact. Rewrite using `[← symplO_smul, (mem_half S WW).1 hx] at this, hx⟩)` and apply the resulting hypothesis.

Use the proof step `(half_div S WW e) (half_div S WW _) tf`. Use the proof step `(fun k hk => by`. Take `⟨R, hR, h⟩` from `hfin k hk`. Use `⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, u, hu, htr⟩` from `h t ht.1`.

Use `⟨_, ⟨r, hr, rfl⟩, e • u, hsm e hee u hu, ?_⟩` and prove the remaining obligations. Use `(mem_half S WW).1 ht.2` as an intermediate fact. Rewrite using `[← this, htr, smul_add, smul_comm e k u])`. Use `_ (fun x => stdFst_mem hν.1 he _ A WW X.rA.β X.rW.β x) (fun t ht => (isHalf_iff S WW).1 (h1 t ht)) k hk`. Use the proof step `(fun u hu => h2 u hu.1 ((isHalf_iff S WW).2 hu.2))`.

Use the proof step `(fun t ht => ⟨h3 t ht, (half S WW e).nsmul_mem ((isHalf_iff S WW).1 (h1 t ht)) _⟩)`. Use `set V : Submodule Qb (WO S WW → ℂ) := Submodule.span Qb {F | ∃ w : WO S WW, w.map (infPart D) = 0 ∧ F = heisO W.ψ S WW w X.vac} with hV`. Establish `hvac : Tm (halfInd e Λ) = X.vac` using `by simpa using hTm.vac`. Establish `s0` using `GlobalTheory.isSBHalf_halfInd e Λ`. Establish `hT : ∀ Ψ ∈ algSpan (fun x y : WO S WW => W.ψ (symplO S WW x y)) (half S WW e) (half S WW (cA D e)) (Λ ⊓ half S WW e), Tm Ψ ∈ V`.

Introduce `Ψ hΨ`. Proceed by induction on `hΨ using Submodule.span_induction with`. Consider the case `mem _ hh`. Take `⟨x, hx, y, hy, rfl⟩` from `hh`. Establish `s1 : IsSBHalf e Λ fun t => W.ψ (symplO S WW t y) * halfInd e Λ t`.

Take `⟨k, hk, hk'⟩` from `GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' (S := S) (T := WW) hSd.1 hWd.1 y (finY y hy)`. Take `⟨a1, k', hk1, a2, a3⟩` from `s0`. Use `⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Establish `e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t`. Rewrite using `[mul_nsmul]`.

Conclude with `a2 _ (nsmul_mem hu k) ((isHalf_iff S WW).2 (nsmul_mem ((isHalf_iff S WW).1 hh) k)) t`. Establish `e2 : W.ψ (symplO S WW ((k * k') • u) y) = 1`. Rewrite using `[mul_nsmul']`. Use `(hb.nsmul k _ y).trans ((hdual _ (finX _ (nsmul_mem ((isHalf_iff S WW).1 hh) k'))).1 (nsmul_mem hu k') _ hk')` and prove the remaining obligations. Simplify using `only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]`.

Rewrite using `[mul_nsmul']`. Conclude with `nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k`. Establish `e1 : wave (fun x y : WO S WW => W.ψ (symplO S WW x y)) (Λ ⊓ half S WW e) x y = fun t => (fun t => W.ψ (symplO S WW t y) * halfInd e Λ t) (t + x)`. Rewrite using `[halfInd_eq_ind]`. Both sides reduce to the same expression.

Rewrite using `[e1, hTm.trans _ s1 x ((isHalf_iff S WW).2 hx), hTm.modul _ s0 y ((isHalf_iff S WW).2 hy), hvac]`. Establish `e2 : heisO W.ψ S WW x (heisO W.ψ S WW y X.vac) = W.ψ (symplOH S WW x y) • heisO W.ψ S WW (x + y) X.vac` using `heisL_heisL S WW W.ψ x y X.vac`. Rewrite using `[e2]`. Use `smul_mem_of_mem (psiH_mem hψ hSd hWd (finX x hx) (finY y hy)) (Submodule.subset_span ⟨x + y, ?_, rfl⟩)` and prove the remaining obligations. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Establish `q1 : infPart D (x a b) = 0` using `congrFun (congrFun (finX x hx) a) b`. Establish `q2 : infPart D (y a b) = 0` using `congrFun (congrFun (finY y hy) a) b`. Express the relevant statement in the definitionally equal form `infPart D (x a b + y a b) = 0`. Rewrite using `[RingHom.map_add, q1, q2, add_zero]`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add f g _ _ hf hg => rw [map_add]`. Conclude with `add_mem hf hg`. Consider the case `smul c f _ hf`. Express the relevant statement in the definitionally equal form `Tm ((c : ℂ) • f) ∈ V`.

Rewrite using `[map_smul]`. Conclude with `V.smul_mem c hf`. Take `⟨n, f, g, hfg⟩` from `(Submodule.mem_span_set').1 (hT _ hmem)`. Use `choose w hw hgw using fun p => (g p).2`. Use `⟨n, fun p => (f p : ℂ), w, fun p => mem_algebraicClosure_iff.1 (f p).2, hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hfg]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← hgw p]`. Both sides reduce to the same expression.
-/
theorem finDatum_eq_sum_heis : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc}
    {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) →
    L.Is μ₀ → IsBottomTri W i j X →
    ∀ t : T, ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
      (∀ p, (w p).map (infPart D) = 0) ∧ X.f t = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t
  classical
  have hI := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hν := (hI.weil' t).hecT
  have hSd : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := by
    refine ⟨hI.rigA.1.1, fun y => (hI.rigA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩,
      fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [GlobalTheory.Grid.neg_gram, hc]
    · simp [GlobalTheory.Grid.neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  have hWd : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  have he := hI.idem t
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hinf' := GlobalTheory.PlaceDatum.infPart_cA hinf
  set S := GlobalTheory.Grid.neg A with hSdef
  set e := X.e t with hedef
  set Λ : AddSubgroup (WO S WW) := latO S WW X.rA.Λ X.rW.Λ fun _ => True with hΛ
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := S) hSd.1 hWd.1 X.rA.β X.rW.β
  have hSB := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_isSB hν.1 he (GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t) A WW X.rA.β X.rW.β Λ
    (GlobalTheory.PlaceDatum.exists_den_frMapO (S := S) hSd.1.fg hWd.1.fg X.rA.β X.rW.β)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hI.fst t
  rw [hall Tm hTm]

  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D W.ψ S WW X.rA.Λ X.rW.Λ hψ hSd hWd).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S WW _ _ hSd.1.fg hWd.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ ⊓ half S WW a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S WW _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have finX : ∀ x ∈ half S WW e, x.map (infPart D) = 0 := fun x hx =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf ((isHalf_iff S WW).2 hx)
  have finY : ∀ y ∈ half S WW (cA D e), y.map (infPart D) = 0 := fun y hy =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf' ((isHalf_iff S WW).2 hy)
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S WW => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S WW hk a, ← inv_smul_nsmul S WW hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S WW W.ψ

  obtain ⟨h1, k, hk, h2, h3⟩ := hSB
  have hmem := mem_algSpan (χ := fun x y : WO S WW => W.ψ (symplO S WW x y)) (X := half S WW e)
    (Y := half S WW (cA D e)) (L := Λ ⊓ half S WW e) (L' := Λ ⊓ half S WW (cA D e)) hb
    (fun x hx y hy => psi_mem hψ hSd hWd (finX x hx) (finY y hy)) inf_le_right inf_le_right
    (fun u hu y hy => (hdual u (finX u hu.2)).1 hu.1 y hy.1)
    (fun x hx h => ⟨(hdual x (finX x hx)).2 fun u hu => by
      have := h _ (hsm _ he' u hu)
      rwa [← symplO_smul, (mem_half S WW).1 hx] at this, hx⟩)
    (half_div S WW e) (half_div S WW _) tf
    (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e hee u hu, ?_⟩
      have := (mem_half S WW).1 ht.2
      rw [← this, htr, smul_add, smul_comm e k u])
    _ (fun x => stdFst_mem hν.1 he _ A WW X.rA.β X.rW.β x) (fun t ht => (isHalf_iff S WW).1 (h1 t ht)) k hk
    (fun u hu => h2 u hu.1 ((isHalf_iff S WW).2 hu.2))
    (fun t ht => ⟨h3 t ht, (half S WW e).nsmul_mem ((isHalf_iff S WW).1 (h1 t ht)) _⟩)

  set V : Submodule Qb (WO S WW → ℂ) := Submodule.span Qb
    {F | ∃ w : WO S WW, w.map (infPart D) = 0 ∧ F = heisO W.ψ S WW w X.vac} with hV
  have hvac : Tm (halfInd e Λ) = X.vac := by simpa using hTm.vac
  have s0 := GlobalTheory.isSBHalf_halfInd e Λ
  have hT : ∀ Ψ ∈ algSpan (fun x y : WO S WW => W.ψ (symplO S WW x y)) (half S WW e) (half S WW (cA D e))
      (Λ ⊓ half S WW e), Tm Ψ ∈ V := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem _ hh =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hh
      have s1 : IsSBHalf e Λ fun t => W.ψ (symplO S WW t y) * halfInd e Λ t := by
        obtain ⟨k, hk, hk'⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' (S := S) (T := WW) hSd.1 hWd.1 y (finY y hy)
        obtain ⟨a1, k', hk1, a2, a3⟩ := s0
        refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
          fun t ht => ?_⟩
        · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
            rw [mul_nsmul]
            exact a2 _ (nsmul_mem hu k) ((isHalf_iff S WW).2 (nsmul_mem ((isHalf_iff S WW).1 hh) k)) t
          have e2 : W.ψ (symplO S WW ((k * k') • u) y) = 1 := by
            rw [mul_nsmul']
            refine (hb.nsmul k _ y).trans ((hdual _ (finX _ (nsmul_mem ((isHalf_iff S WW).1 hh) k'))).1
              (nsmul_mem hu k') _ hk')
          simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
        · rw [mul_nsmul']
          exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
      have e1 : wave (fun x y : WO S WW => W.ψ (symplO S WW x y)) (Λ ⊓ half S WW e) x y =
          fun t => (fun t => W.ψ (symplO S WW t y) * halfInd e Λ t) (t + x) := by
        rw [halfInd_eq_ind]; rfl
      rw [e1, hTm.trans _ s1 x ((isHalf_iff S WW).2 hx), hTm.modul _ s0 y ((isHalf_iff S WW).2 hy), hvac]
      have e2 : heisO W.ψ S WW x (heisO W.ψ S WW y X.vac) =
          W.ψ (symplOH S WW x y) • heisO W.ψ S WW (x + y) X.vac := heisL_heisL S WW W.ψ x y X.vac
      rw [e2]
      refine smul_mem_of_mem (psiH_mem hψ hSd hWd (finX x hx) (finY y hy)) (Submodule.subset_span ⟨x + y, ?_, rfl⟩)
      refine Matrix.ext fun a b => ?_
      have q1 : infPart D (x a b) = 0 := congrFun (congrFun (finX x hx) a) b
      have q2 : infPart D (y a b) = 0 := congrFun (congrFun (finY y hy) a) b
      change infPart D (x a b + y a b) = 0
      rw [RingHom.map_add, q1, q2, add_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
    | smul c f _ hf =>
      change Tm ((c : ℂ) • f) ∈ V
      rw [map_smul]
      exact V.smul_mem c hf
  obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').1 (hT _ hmem)
  choose w hw hgw using fun p => (g p).2
  refine ⟨n, fun p => (f p : ℂ), w, fun p => mem_algebraicClosure_iff.1 (f p).2, hw, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hgw p]
  rfl

end GlobalTheory.BotFourier
