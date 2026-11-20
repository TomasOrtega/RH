import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PerIntOnAmb
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGapNonemptyAndRecordNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisor

noncomputable section

namespace GlobalTheory.Core.Int.Model

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

section General

variable (D : D7) (u : D.what₂.Word)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vGam_eq (w : D.what₂.places.Pl) : vGam D u w = WeilJacquetShalikaLaw.vDG D u w := rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem colGe_iff (w : D.what₂.places.Pl) (x : ((D.fm u).lat 0).V) (s : ℝ) :
    ColGe D u w x s ↔ WeilJacquetShalikaLaw.ColGe0 D u w x s := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem nprime_iff (L : SizeData₂ D) : DV.NprimeDef D L ↔
    ∀ u, (D.div.Nu u).L = shift D u L.supp (fun w => ⌊DV.ur D w (L.sg u w)⌋) (L.NuLat u) := Iff.rfl

/- English proof (translation)
Introduce `_ u x hx F hF _` and use `h u x hx F hF`.
-/
theorem admissiblePeriod_of_periodInt (h : ∀ u, PeriodInt D u) : WeightDegreeSizes.PeriodClassSumWeyl D :=
  fun _ u x hx F hF _ => h u x hx F hF

/- English proof (translation)
Introduce `u w φ hφ`. Rewrite using `[hμ w]`. Conclude with `fun F hF _ => h u w φ hφ F hF`.
-/
theorem second_hypothesis_of_lifting (L : SizeData₂ D) (hμ : ∀ w, D.what₂.muAt w = D.what₂.mu0)
    (h : ∀ u w, PerGeOn D u (L.NuLat u) w ((⌊DV.ur D w (L.sg u w)⌋ : ℤ) : ℝ)) : LocalQuadraticParts.adm2 D L := by
  intro u w φ hφ
  rw [hμ w]
  exact fun F hF _ => h u w φ hφ F hF

variable {D}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨y', h, hv⟩ => D.what₂.embLL.injective h ▸ hv, fun h => ⟨y, rfl, h⟩⟩`.
-/
theorem valGe_emb (w : D.what₂.places.Pl) (y : D.what₂.LL) (s : ℝ) :
    ValGe D w (D.what₂.embLL y) s ↔ (y = 0 ∨ s ≤ (vAdd (D.plEq w) y : ℝ)) :=
  ⟨fun ⟨y', h, hv⟩ => D.what₂.embLL.injective h ▸ hv, fun h => ⟨y, rfl, h⟩⟩

/- English proof (translation)
Establish `h1` using `D.what₂.places.val_resChar w`. Rewrite `h1` using `[D.val_eq w _ (Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero)]`. Conclude with `h1` after adjusting the coercions.
-/
theorem vAdd_resChar (w : D.what₂.places.Pl) :
    vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℕ) := by
  have h1 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ (Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero)] at h1
  exact_mod_cast h1

/- English proof (translation)
Rewrite using `[← map_natCast D.what₂.embLL, valGe_emb, vAdd_resChar]`. Establish `: ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0` using `Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero`. Simplify using `[this]`.
-/
theorem valGe_resChar (w : D.what₂.places.Pl) (s : ℝ) :
    ValGe D w ((D.what₂.places.resChar w : ℕ) : ℂ) s ↔ s ≤ (D.what₂.places.ramIdx w : ℝ) := by
  rw [← map_natCast D.what₂.embLL, valGe_emb, vAdd_resChar]
  have : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  simp [this]

/- English proof (translation)
Simplify using `[vAdd]`.
-/
theorem vAdd_inv (w : D.what₂.places.Pl) (y : D.what₂.LL) : vAdd (D.plEq w) y⁻¹ = - vAdd (D.plEq w) y := by
  simp [vAdd]

/- English proof (translation)
Rewrite using `[← map_natCast D.what₂.embLL, ← map_inv₀, valGe_emb, vAdd_inv, vAdd_resChar]`. Establish `h : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0` using `Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero`. Use `D.what₂.places.ramIdx_pos w` as an intermediate fact. Simplify using `[h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_valGe_inv (w : D.what₂.places.Pl) : ¬ ValGe D w ((D.what₂.places.resChar w : ℕ) : ℂ)⁻¹ 0 := by
  rw [← map_natCast D.what₂.embLL, ← map_inv₀, valGe_emb, vAdd_inv, vAdd_resChar]
  have h : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have := D.what₂.places.ramIdx_pos w
  simp [h]; omega

/- English proof (translation)
Introduce `⟨y, hy, _⟩` and use `hz ⟨y, hy⟩`.
-/
theorem not_valGe_of_notMem (w : D.what₂.places.Pl) {z : ℂ} (hz : z ∉ Set.range D.what₂.embLL) (s : ℝ) : ¬ ValGe D w z s :=
  fun ⟨y, hy, _⟩ => hz ⟨y, hy⟩

/- English proof (translation)
Unfold `ValGe`. Simplify using `only [Int.cast_le, Int.ceil_le]`.
-/
theorem valGe_ceil (w : D.what₂.places.Pl) (z : ℂ) (s : ℝ) : ValGe D w z s ↔ ValGe D w z ((⌈s⌉ : ℤ) : ℝ) := by
  unfold ValGe
  simp only [Int.cast_le, Int.ceil_le]

/- English proof (translation)
The claim follows from `let ⟨y, hy, hv⟩ := h ⟨y, hy, hv.imp id hst.trans⟩`.
-/
theorem valGe_mono {w : D.what₂.places.Pl} {z : ℂ} {s t : ℝ} (hst : t ≤ s) (h : ValGe D w z s) : ValGe D w z t :=
  let ⟨y, hy, hv⟩ := h
  ⟨y, hy, hv.imp id hst.trans⟩

/- English proof (translation)
Take `⟨y, rfl, hv⟩` from `h`. Take `⟨y', rfl, hv'⟩` from `h'`. Use `⟨y * y', map_mul _ _ _, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : y = 0`. Simplify using `[h0]`.

Distinguish the cases in `h1 : y' = 0`. Simplify using `[h1]`. Use `right`. Rewrite using `[WeilJacquetShalikaLaw.vAdd_mul' _ h0 h1]`. Use `push_cast`.

Conclude with `add_le_add (hv.resolve_left h0) (hv'.resolve_left h1)`.
-/
theorem valGe_mul {w : D.what₂.places.Pl} {z z' : ℂ} {s t : ℝ} (h : ValGe D w z s) (h' : ValGe D w z' t) :
    ValGe D w (z * z') (s + t) := by
  obtain ⟨y, rfl, hv⟩ := h
  obtain ⟨y', rfl, hv'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · simp [h0]
  by_cases h1 : y' = 0
  · simp [h1]
  right
  rw [WeilJacquetShalikaLaw.vAdd_mul' _ h0 h1]
  push_cast
  exact add_le_add (hv.resolve_left h0) (hv'.resolve_left h1)

/- English proof (translation)
Take `⟨y, rfl, hv⟩` from `h`. Take `⟨y', rfl, hv'⟩` from `h'`. Conclude with `⟨y + y', map_add _ _ _, WeightDegreeSizes.pair_add_ge D w hv hv'⟩`.
-/
theorem valGe_add {w : D.what₂.places.Pl} {z z' : ℂ} {s : ℝ} (h : ValGe D w z s) (h' : ValGe D w z' s) :
    ValGe D w (z + z') s := by
  obtain ⟨y, rfl, hv⟩ := h
  obtain ⟨y', rfl, hv'⟩ := h'
  exact ⟨y + y', map_add _ _ _, WeightDegreeSizes.pair_add_ge D w hv hv'⟩

/- English proof (translation)
Rewrite using `[valGe_emb]`. Distinguish the cases in `h : (a : D.what₂.LL) = 0`. Conclude with `Or.inl h`. Use `right`. Establish `h1 : (0 : WithTop ℤ) ≤ D.what₂.places.val w a` using `a.2`.

Rewrite `h1` using `[D.val_eq w _ h]`. Conclude with `h1` after adjusting the coercions.
-/
theorem valGe_of_mem_intW {w : D.what₂.places.Pl} (a : intW D.what₂.places w) : ValGe D w (D.what₂.embLL a) 0 := by
  rw [valGe_emb]
  by_cases h : (a : D.what₂.LL) = 0
  · exact Or.inl h
  right
  have h1 : (0 : WithTop ℤ) ≤ D.what₂.places.val w a := a.2
  rw [D.val_eq w _ h] at h1
  exact_mod_cast h1

/- English proof (translation)
Take `⟨hR, hI⟩` from `h1`. Introduce `z hz F hF`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, hv⟩` from `h2 _ (hI x hx) F hF`.

Rewrite `hy` using `[(D.fm u).PtL_spec]`. Conclude with `⟨y, hy, hv w⟩`. Consider the case `zero => exact ⟨0, by simp [PeriodMap.Ptil], Or.inl rfl⟩`. Consider the case `add x y _ _ hx hy`. Use `valGe_add hx hy` as an intermediate fact.

Simplify `this` using `[PeriodMap.Ptil]`. Consider the case `smul a x _ hx`. Use `valGe_mul (valGe_of_mem_intW a) hx` as an intermediate fact. Rewrite `this` using `[zero_add]`. Establish `e : a • x = (a : D.what₂.LL) • x` using `rfl`.

Rewrite using `[e, LinearMap.map_smulₛₗ]`. Simplify `this` using `[PeriodMap.Ptil]`.
-/
theorem pairInt_of (h1 : PtInt D u) (h2 : PeriodInt D u) (w : D.what₂.places.Pl) : PairInt D u w := by
  obtain ⟨hR, hI⟩ := h1
  intro z hz F hF
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, hv⟩ := h2 _ (hI x hx) F hF
    rw [(D.fm u).PtL_spec] at hy
    exact ⟨y, hy, hv w⟩
  | zero => exact ⟨0, by simp [PeriodMap.Ptil], Or.inl rfl⟩
  | add x y _ _ hx hy =>
    have := valGe_add hx hy
    simpa [PeriodMap.Ptil] using this
  | smul a x _ hx =>
    have := valGe_mul (valGe_of_mem_intW a) hx
    rw [zero_add] at this
    have e : a • x = (a : D.what₂.LL) • x := rfl
    rw [e, LinearMap.map_smulₛₗ]
    simpa [PeriodMap.Ptil] using this

/- English proof (translation)
Introduce `φ hφ F hF`. Take `⟨y, hy, a, z, hz, rfl, ha⟩` from `h1 φ hφ`. Use `valGe_mul ((valGe_emb w a _).2 ha) (h2 z hz F hF)` as an intermediate fact. Rewrite using `[D.perCol_base_eq_PtilCol, D.nuIn_jN, PeriodMap.PtilCol, ← hy, LinearMap.map_smulₛₗ, mul_sub, sub_eq_add_neg]`. Simplify `this` using `[PeriodMap.Ptil]`.
-/
theorem perGeOn_of {N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V} {w : D.what₂.places.Pl} {s : ℝ}
    (h1 : ColGeOn D u N w s) (h2 : PairInt D u w) :
    PerGeOn D u N w ((D.what₂.places.ramIdx w : ℝ) * (s - vGam D u w)) := by
  intro φ hφ F hF
  obtain ⟨y, hy, a, z, hz, rfl, ha⟩ := h1 φ hφ
  have := valGe_mul ((valGe_emb w a _).2 ha) (h2 z hz F hF)
  rw [D.perCol_base_eq_PtilCol, D.nuIn_jN, PeriodMap.PtilCol, ← hy, LinearMap.map_smulₛₗ, mul_sub, sub_eq_add_neg]
  simpa [PeriodMap.Ptil] using this

/- English proof (translation)
Rewrite using `[LinearMap.map_smulₛₗ]`. Simplify using `only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, Examples₂.NZ.col_smul]`. Simplify using the standard rewrite rules.
-/
theorem per_smul (a : D.what₂.LL) (φ : (D.div.Nu u).V) (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 (D.jN u (a • φ)) F = D.what₂.embLL a * D.what₂.perCol u D.what₂.mu0 (D.jN u φ) F := by
  rw [LinearMap.map_smulₛₗ]
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, Examples₂.NZ.col_smul]
  simp

/- English proof (translation)
Simplify using `only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_add, Submodule.coe_add, Examples₂.NZ.col_add]`. Simplify using the standard rewrite rules.
-/
theorem per_add (φ ψ : (D.div.Nu u).V) (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 (D.jN u (φ + ψ)) F =
      D.what₂.perCol u D.what₂.mu0 (D.jN u φ) F + D.what₂.perCol u D.what₂.mu0 (D.jN u ψ) F := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_add, Submodule.coe_add, Examples₂.NZ.col_add]
  simp

/- English proof (translation)
Take `⟨y, rfl, -⟩` from `h w0`. Establish `: ∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), v.valuation D.what₂.LL y ≤ 1`. Introduce `v`. Take `⟨w, rfl⟩` from `D.plEq.surjective v`. Distinguish the cases in `h0 : y = 0`.

Simplify using `[h0]`. Establish `h1` using `((valGe_emb w y 0).1 (h w)).resolve_left h0`. Establish `h2 : (0 : ℤ) ≤ vAdd (D.plEq w) y` using `by exact_mod_cast h1`. Unfold `vAdd at h2`. Establish `hne : (D.plEq w).valuation D.what₂.LL y ≠ 0` using `by simpa using h0`.

Rewrite using `[← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Take `⟨c, hc⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one D.what₂.LL y this`. Conclude with `⟨c, congrArg _ hc⟩`.
-/
theorem int_of_valGe {z : ℂ} (h : ∀ w, ValGe D w z 0) (w0 : D.what₂.places.Pl) :
    ∃ y : 𝓞 D.what₂.LL, D.what₂.embLL (y : D.what₂.LL) = z := by
  obtain ⟨y, rfl, -⟩ := h w0
  have : ∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), v.valuation D.what₂.LL y ≤ 1 := by
    intro v
    obtain ⟨w, rfl⟩ := D.plEq.surjective v
    by_cases h0 : y = 0
    · simp [h0]
    have h1 := ((valGe_emb w y 0).1 (h w)).resolve_left h0
    have h2 : (0 : ℤ) ≤ vAdd (D.plEq w) y := by exact_mod_cast h1
    unfold vAdd at h2
    have hne : (D.plEq w).valuation D.what₂.LL y ≠ 0 := by simpa using h0
    rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one D.what₂.LL y this
  exact ⟨c, congrArg _ hc⟩

/- English proof (translation)
Rewrite using `[valGe_emb]`. Distinguish the cases in `h0 : (y : D.what₂.LL) = 0`. Conclude with `Or.inl h0`. Use `right`. Establish `h1 : (D.plEq w).valuation D.what₂.LL (y : D.what₂.LL) ≤ 1` using `(D.plEq w).valuation_le_one y`.

Establish `hne : (D.plEq w).valuation D.what₂.LL (y : D.what₂.LL) ≠ 0` using `by simpa using h0`. Rewrite `h1` using `[← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Establish `: (0 : ℤ) ≤ vAdd (D.plEq w) (y : D.what₂.LL)` using `by unfold vAdd; omega`. Conclude with `this` after adjusting the coercions.
-/
theorem valGe_of_int (w : D.what₂.places.Pl) (y : 𝓞 D.what₂.LL) : ValGe D w (D.what₂.embLL (y : D.what₂.LL)) 0 := by
  rw [valGe_emb]
  by_cases h0 : (y : D.what₂.LL) = 0
  · exact Or.inl h0
  right
  have h1 : (D.plEq w).valuation D.what₂.LL (y : D.what₂.LL) ≤ 1 := (D.plEq w).valuation_le_one y
  have hne : (D.plEq w).valuation D.what₂.LL (y : D.what₂.LL) ≠ 0 := by simpa using h0
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  have : (0 : ℤ) ≤ vAdd (D.plEq w) (y : D.what₂.LL) := by unfold vAdd; omega
  exact_mod_cast this

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 D.what₂.LL)`. Conclude with `⟨D.plEq.symm ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩`.
-/
theorem nonempty_place : Nonempty D.what₂.places.Pl := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.what₂.LL)
  exact ⟨D.plEq.symm ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩

/- English proof (translation)
Take `⟨w0⟩` from `nonempty_place (D := D)`. Prove the components needed by the constructor for the conclusion. Introduce `h w φ hφ F hF`. Take `⟨y, hy⟩` from `h φ hφ F hF`. Conclude with `hy ▸ valGe_of_int w y`.

Introduce `h φ hφ F hF`. Conclude with `int_of_valGe (fun w => h w φ hφ F hF) w0`.
-/
theorem perIntOn_iff (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : PerIntOn D u N ↔ ∀ w, PerGeOn D u N w 0 := by
  obtain ⟨w0⟩ := nonempty_place (D := D)
  constructor
  · intro h w φ hφ F hF
    obtain ⟨y, hy⟩ := h φ hφ F hF
    exact hy ▸ valGe_of_int w y
  · intro h φ hφ F hF
    exact int_of_valGe (fun w => h w φ hφ F hF) w0

open Classical in
/- English proof (translation)
Rewrite using `[FractionalIdeal.count_prod _ _ _ _ (fun b _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq b).ne_bot))]`. Establish `h0 : ∀ b, b ≠ w → FractionalIdeal.count D.what₂.LL (D.plEq w) (((D.plEq b).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-(n b))) = 0` using `fun b hb => by`. Rewrite using `[FractionalIdeal.count_zpow, FractionalIdeal.count_maximal_coprime _ _ (fun h => hb (D.plEq.injective h)), mul_zero]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single w (fun b _ hb => h0 b hb) (fun h' => (h' h).elim), FractionalIdeal.count_zpow_self]`.

Conclude with `Finset.sum_eq_zero fun b hb => h0 b (fun e => h (e ▸ hb))`.
-/
theorem count_shift (S : Finset D.what₂.places.Pl) (n : D.what₂.places.Pl → ℤ) (w : D.what₂.places.Pl) :
    FractionalIdeal.count D.what₂.LL (D.plEq w)
      (∏ w ∈ S, ((D.plEq w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-(n w))) =
      if w ∈ S then - n w else 0 := by
  rw [FractionalIdeal.count_prod _ _ _ _
    (fun b _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq b).ne_bot))]
  have h0 : ∀ b, b ≠ w → FractionalIdeal.count D.what₂.LL (D.plEq w)
      (((D.plEq b).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-(n b))) = 0 := fun b hb => by
    rw [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal_coprime _ _ (fun h => hb (D.plEq.injective h)), mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single w (fun b _ hb => h0 b hb) (fun h' => (h' h).elim), FractionalIdeal.count_zpow_self]
  · exact Finset.sum_eq_zero fun b hb => h0 b (fun e => h (e ▸ hb))

/- English proof (translation)
Unfold `vAdd`. Rewrite using `[NumeratorIdeal.valuation_eq_count _ _ hy, WithZero.log_exp, neg_neg]`.
-/
theorem vAdd_eq_count (w : D.what₂.places.Pl) {y : D.what₂.LL} (hy : y ≠ 0) :
    vAdd (D.plEq w) y = FractionalIdeal.count D.what₂.LL (D.plEq w)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) y) := by
  unfold vAdd
  rw [NumeratorIdeal.valuation_eq_count _ _ hy, WithZero.log_exp, neg_neg]

open Classical in

/- English proof (translation)
Use `set I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL := ∏ w ∈ S, ((D.plEq w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-(n w)) with hI`. Establish `hI0 : I ≠ 0` using `Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq b).ne_bot)`. Establish `hc : ∀ w, FractionalIdeal.count D.what₂.LL (D.plEq w) I = - (if w ∈ S then n w else 0)` using `fun w => by`. Apply the tactic sequence `rw [hI, count_shift]; split_ifs <;> simp`. Prove the components needed by the constructor for the conclusion.

Introduce `h w φ hφ F hF`. Establish `h1 : ∀ a ∈ I, ∃ y : 𝓞 D.what₂.LL, D.what₂.embLL (y : D.what₂.LL) = D.what₂.embLL a * D.what₂.perCol u D.what₂.mu0 (D.jN u φ) F` using `fun a ha => by`. Rewrite using `[← per_smul]`. Conclude with `h _ (Submodule.subset_span ⟨a, ha, φ, hφ, rfl⟩) F hF`. Choose the witnesses or unpack the hypotheses as in `⟨a0, ha0, ha0I⟩ : ∃ a : D.what₂.LL, a ≠ 0 ∧ a ∈ I := by`.

Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Apply `hI0` to reduce the goal to its premises. Rewrite using `[FractionalIdeal.eq_zero_iff]`. Introduce `x hx`.

Assume the negation of the conclusion as `hx0`. Conclude with `hn x hx0 hx`. Take `⟨y0, hy0⟩` from `h1 a0 ha0I`. Establish `he : D.what₂.embLL a0 ≠ 0` using `(map_ne_zero _).2 ha0`. Establish `hy : D.what₂.embLL (y0 / a0) = D.what₂.perCol u D.what₂.mu0 (D.jN u φ) F`.

Rewrite using `[map_div₀, hy0]`. Clear the denominators using the available nonvanishing facts. Generalize the expression as in `(y0 : D.what₂.LL) / a0 = y at hy`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hy0 : y = 0`.

Conclude with `Or.inl hy0`. Use `right`. Establish `hs : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) y ≠ 0` using `FractionalIdeal.spanSingleton_ne_zero_iff.2 hy0`. Establish `hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) y * I ≤ 1`. Introduce `x hx`.

Take `⟨a, ha, rfl⟩` from `FractionalIdeal.mem_singleton_mul.1 hx`. Take `⟨c, hc⟩` from `h1 a ha`. Rewrite `hc` using `[← hy, ← map_mul]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨c, by rw [mul_comm]; exact D.what₂.embLL.injective hc⟩`. Establish `h2` using `FractionalIdeal.count_mono D.what₂.LL (D.plEq w) (mul_ne_zero hs hI0) hle`.

Rewrite `h2` using `[FractionalIdeal.count_one, FractionalIdeal.count_mul _ _ hs hI0, hc, ← vAdd_eq_count w hy0]`. Establish `h3 : (if w ∈ S then n w else 0) ≤ vAdd (D.plEq w) y` using `by omega`. Conclude with `h3` after adjusting the coercions. Introduce `h`. Rewrite using `[perIntOn_iff]`.

Introduce `w φ hφ F hF`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, y, hy, rfl⟩` from `hx`. Rewrite using `[per_smul]`.

Establish `h1 : ValGe D w (D.what₂.embLL a) (-(((if w ∈ S then n w else 0 : ℤ)) : ℝ))`. Rewrite using `[valGe_emb]`. Distinguish the cases in `ha0 : a = 0`. Conclude with `Or.inl ha0`. Use `right`.

Establish `h2` using `FractionalIdeal.count_mono D.what₂.LL (D.plEq w) (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0) (FractionalIdeal.spanSingleton_le_iff_mem.2 ha)`. Rewrite `h2` using `[hc, ← vAdd_eq_count w ha0]`. Conclude with `h2` after adjusting the coercions. Simplify using `using valGe_mul h1 (h w y hy F hF)`. Consider the case `zero`.

Use `per_smul u 0 0 F` as an intermediate fact. Rewrite `this` using `[zero_smul, map_zero D.what₂.embLL, zero_mul]`. Conclude with `⟨0, by rw [this, map_zero], Or.inl rfl⟩`. Consider the case `add x y _ _ hx hy => rw [per_add]`. Conclude with `valGe_add hx hy`.

Consider the case `smul a x _ hx`. Rewrite using `[show a • x = (a : D.what₂.LL) • x from (algebraMap_smul D.what₂.LL a x).symm, per_smul]`. Simplify using `using valGe_mul (valGe_of_int w a) hx`.
-/
theorem perIntOn_shift_iff (S : Finset D.what₂.places.Pl) (n : D.what₂.places.Pl → ℤ)
    (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) :
    PerIntOn D u (shift D u S n N) ↔ ∀ w, PerGeOn D u N w (((if w ∈ S then n w else 0 : ℤ)) : ℝ) := by
  set I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL :=
    ∏ w ∈ S, ((D.plEq w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-(n w)) with hI
  have hI0 : I ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq b).ne_bot)
  have hc : ∀ w, FractionalIdeal.count D.what₂.LL (D.plEq w) I = - (if w ∈ S then n w else 0) := fun w => by
    rw [hI, count_shift]; split_ifs <;> simp
  constructor
  · intro h w φ hφ F hF
    have h1 : ∀ a ∈ I, ∃ y : 𝓞 D.what₂.LL, D.what₂.embLL (y : D.what₂.LL) =
        D.what₂.embLL a * D.what₂.perCol u D.what₂.mu0 (D.jN u φ) F := fun a ha => by
      rw [← per_smul]
      exact h _ (Submodule.subset_span ⟨a, ha, φ, hφ, rfl⟩) F hF
    obtain ⟨a0, ha0, ha0I⟩ : ∃ a : D.what₂.LL, a ≠ 0 ∧ a ∈ I := by
      by_contra hn
      push_neg at hn
      apply hI0
      rw [FractionalIdeal.eq_zero_iff]
      intro x hx
      by_contra hx0
      exact hn x hx0 hx
    obtain ⟨y0, hy0⟩ := h1 a0 ha0I
    have he : D.what₂.embLL a0 ≠ 0 := (map_ne_zero _).2 ha0
    have hy : D.what₂.embLL (y0 / a0) = D.what₂.perCol u D.what₂.mu0 (D.jN u φ) F := by
      rw [map_div₀, hy0]; field_simp
    generalize (y0 : D.what₂.LL) / a0 = y at hy
    refine ⟨y, hy, ?_⟩
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    right
    have hs : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) y ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.2 hy0
    have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) y * I ≤ 1 := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hx
      obtain ⟨c, hc⟩ := h1 a ha
      rw [← hy, ← map_mul] at hc
      exact (FractionalIdeal.mem_one_iff _).2 ⟨c, by rw [mul_comm]; exact D.what₂.embLL.injective hc⟩
    have h2 := FractionalIdeal.count_mono D.what₂.LL (D.plEq w) (mul_ne_zero hs hI0) hle
    rw [FractionalIdeal.count_one, FractionalIdeal.count_mul _ _ hs hI0, hc, ← vAdd_eq_count w hy0] at h2
    have h3 : (if w ∈ S then n w else 0) ≤ vAdd (D.plEq w) y := by omega
    exact_mod_cast h3
  · intro h
    rw [perIntOn_iff]
    intro w φ hφ F hF
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hx
      rw [per_smul]
      have h1 : ValGe D w (D.what₂.embLL a) (-(((if w ∈ S then n w else 0 : ℤ)) : ℝ)) := by
        rw [valGe_emb]
        by_cases ha0 : a = 0
        · exact Or.inl ha0
        right
        have h2 := FractionalIdeal.count_mono D.what₂.LL (D.plEq w) (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0)
          (FractionalIdeal.spanSingleton_le_iff_mem.2 ha)
        rw [hc, ← vAdd_eq_count w ha0] at h2
        exact_mod_cast h2
      simpa using valGe_mul h1 (h w y hy F hF)
    | zero =>
      have := per_smul u 0 0 F
      rw [zero_smul, map_zero D.what₂.embLL, zero_mul] at this
      exact ⟨0, by rw [this, map_zero], Or.inl rfl⟩
    | add x y _ _ hx hy => rw [per_add]; exact valGe_add hx hy
    | smul a x _ hx =>
      rw [show a • x = (a : D.what₂.LL) • x from (algebraMap_smul D.what₂.LL a x).symm, per_smul]
      simpa using valGe_mul (valGe_of_int w a) hx

/- English proof (translation)
Use `⟨fun x => if x = v then 1 else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (fun h => (h hv).elim)]`. Simplify using the standard rewrite rules.
-/
theorem gen_mem (μ : D.what₂.Tup) {v : D.what₂.Amb μ} (hv : v ∈ (D.what₂.Mtilde μ).gen) : v ∈ (D.what₂.Mtilde μ).carrier := by
  classical
  refine ⟨fun x => if x = v then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (fun h => (h hv).elim)]
  simp

/- English proof (translation)
Establish `lin : ∀ (φ : D.what₂.Mu u) (s : Finset (D.what₂.Amb D.what₂.mu0)) (c : D.what₂.Amb D.what₂.mu0 → ℂ), D.what₂.perCol u D.what₂.mu0 φ (∑ v ∈ s, c v • v) = ∑ v ∈ s, c v * D.what₂.perCol u D.what₂.mu0 φ v`. Introduce `φ s c`. Simplify using `[D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil]`. Prove the components needed by the constructor for the conclusion. Introduce `h φ hφ F hF`.

Take `⟨c, rfl⟩` from `hF`. Establish `hg : ∀ v : D.what₂.Amb D.what₂.mu0, ∃ y : 𝓞 D.what₂.LL, v ∈ (D.what₂.Mtilde D.what₂.mu0).gen → D.what₂.embLL (y : D.what₂.LL) = D.what₂.perCol u D.what₂.mu0 (D.jN u φ) v` using `fun v => by classical`. Distinguish the cases in `hv : v ∈ (D.what₂.Mtilde D.what₂.mu0).gen`. Take `⟨x, hx⟩` from `A.jAmb_gen _ (Or.inl rfl) v hv`. Establish `hxL : x ∈ (A.MtH D.what₂.mu0).L`.

Use `(A.jAmb_lat _ (Or.inl rfl) x).2 ⟨fun x => if x = v then 1 else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`. Use `symm`. Use `(Finset.sum_eq_single (v : (RowSide.sharp D).Amb D.what₂.mu0) (fun b _ hb => ?_) (fun h => (h hv).elim)).trans ?_` and prove the remaining obligations. Use `beta_reduce erw [if_neg hb]`.

Simplify using the standard rewrite rules. Conclude with `zero_smul ℂ (b : D.what₂.Amb D.what₂.mu0)`. Use `beta_reduce erw [if_pos rfl]`. Simplify using the standard rewrite rules. Conclude with `one_smul ℂ (v : D.what₂.Amb D.what₂.mu0)`.

Take `⟨y, hy⟩` from `h φ hφ x hxL`. Conclude with `⟨y, fun _ => hx ▸ hy⟩`. Conclude with `⟨0, fun h => (hv h).elim⟩`. Use `choose y hy using hg`. Use `⟨∑ v ∈ (D.what₂.Mtilde D.what₂.mu0).gen, (show 𝓞 D.what₂.LL from ⟨D.what₂.OtoLL (c v), D.O_int (c v)⟩) * y v, ?_⟩` and prove the remaining obligations.

Rewrite using `[lin]`. Rewrite using `[show ∀ t : 𝓞 D.what₂.LL, (t : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL t from fun _ => rfl, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← hy v hv]`. Both sides reduce to the same expression.

Introduce `h φ hφ z hz`. Take `⟨c, hc⟩` from `(A.jAmb_lat _ (Or.inl rfl) z).1 hz`. Establish `hg : ∀ v : D.what₂.Amb D.what₂.mu0, ∃ y : 𝓞 D.what₂.LL, v ∈ (D.what₂.Mtilde D.what₂.mu0).gen → D.what₂.embLL (y : D.what₂.LL) = D.what₂.perCol u D.what₂.mu0 (D.jN u φ) v` using `fun v => by`. Distinguish the cases in `hv : v ∈ (D.what₂.Mtilde D.what₂.mu0).gen`. Take `⟨y, hy⟩` from `h φ hφ v (gen_mem _ hv)`.

Conclude with `⟨y, fun _ => hy⟩`. Conclude with `⟨0, fun h => (hv h).elim⟩`. Use `choose y hy using hg`. Use `⟨∑ v ∈ (D.what₂.Mtilde D.what₂.mu0).gen, c v * y v, ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`.

Use `Eq.trans ?_ (lin _ _ _).symm` and prove the remaining obligations. Rewrite using `[show ∀ t : 𝓞 D.what₂.LL, (t : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL t from fun _ => rfl, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← hy v hv]`.
-/
theorem perIntOnAmb_iff (A : AmbForm D (RowSide.sharp D)) (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) :
    PerIntOnAmb D u A N ↔ PerIntOn D u N := by
  have lin : ∀ (φ : D.what₂.Mu u) (s : Finset (D.what₂.Amb D.what₂.mu0)) (c : D.what₂.Amb D.what₂.mu0 → ℂ),
      D.what₂.perCol u D.what₂.mu0 φ (∑ v ∈ s, c v • v) = ∑ v ∈ s, c v * D.what₂.perCol u D.what₂.mu0 φ v := by
    intro φ s c
    simp [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil]
  constructor
  · intro h φ hφ F hF
    obtain ⟨c, rfl⟩ := hF
    have hg : ∀ v : D.what₂.Amb D.what₂.mu0, ∃ y : 𝓞 D.what₂.LL, v ∈ (D.what₂.Mtilde D.what₂.mu0).gen →
        D.what₂.embLL (y : D.what₂.LL) = D.what₂.perCol u D.what₂.mu0 (D.jN u φ) v := fun v => by
      classical
      by_cases hv : v ∈ (D.what₂.Mtilde D.what₂.mu0).gen
      · obtain ⟨x, hx⟩ := A.jAmb_gen _ (Or.inl rfl) v hv
        have hxL : x ∈ (A.MtH D.what₂.mu0).L := by
          refine (A.jAmb_lat _ (Or.inl rfl) x).2 ⟨fun x => if x = v then 1 else 0, ?_⟩
          rw [hx]
          symm
          refine (Finset.sum_eq_single (v : (RowSide.sharp D).Amb D.what₂.mu0) (fun b _ hb => ?_) (fun h => (h hv).elim)).trans ?_
          · beta_reduce
            erw [if_neg hb]; simp; exact zero_smul ℂ (b : D.what₂.Amb D.what₂.mu0)
          · beta_reduce
            erw [if_pos rfl]; simp; exact one_smul ℂ (v : D.what₂.Amb D.what₂.mu0)
        obtain ⟨y, hy⟩ := h φ hφ x hxL
        exact ⟨y, fun _ => hx ▸ hy⟩
      · exact ⟨0, fun h => (hv h).elim⟩
    choose y hy using hg
    refine ⟨∑ v ∈ (D.what₂.Mtilde D.what₂.mu0).gen, (show 𝓞 D.what₂.LL from ⟨D.what₂.OtoLL (c v), D.O_int (c v)⟩) * y v, ?_⟩
    rw [lin]
    rw [show ∀ t : 𝓞 D.what₂.LL, (t : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL t from fun _ => rfl, map_sum, map_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [map_mul, map_mul, ← hy v hv]
    rfl
  · intro h φ hφ z hz
    obtain ⟨c, hc⟩ := (A.jAmb_lat _ (Or.inl rfl) z).1 hz
    have hg : ∀ v : D.what₂.Amb D.what₂.mu0, ∃ y : 𝓞 D.what₂.LL, v ∈ (D.what₂.Mtilde D.what₂.mu0).gen →
        D.what₂.embLL (y : D.what₂.LL) = D.what₂.perCol u D.what₂.mu0 (D.jN u φ) v := fun v => by
      by_cases hv : v ∈ (D.what₂.Mtilde D.what₂.mu0).gen
      · obtain ⟨y, hy⟩ := h φ hφ v (gen_mem _ hv)
        exact ⟨y, fun _ => hy⟩
      · exact ⟨0, fun h => (hv h).elim⟩
    choose y hy using hg
    refine ⟨∑ v ∈ (D.what₂.Mtilde D.what₂.mu0).gen, c v * y v, ?_⟩
    rw [hc]
    refine Eq.trans ?_ (lin _ _ _).symm
    rw [show ∀ t : 𝓞 D.what₂.LL, (t : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL t from fun _ => rfl, map_sum, map_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [map_mul, map_mul, ← hy v hv]

/- English proof (translation)
Establish `he : (0 : ℝ) < D.what₂.places.ramIdx w` using `by exact_mod_cast D.what₂.places.ramIdx_pos w`. Establish `h3 : ValGe D w (D.what₂.embLL (l x)) 0` using `by clear h1`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, hc⟩` from `hl x hx`.

Rewrite using `[hc]`. Conclude with `valGe_of_int w c`. Consider the case `zero => exact ⟨0, by simp, Or.inl rfl⟩`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, map_add]`.

Conclude with `valGe_add hx hy`. Consider the case `smul b x _ hx`. Use `valGe_mul (valGe_of_mem_intW b) hx` as an intermediate fact. Rewrite using `[show b • x = (b : D.what₂.LL) • x from rfl, map_smul, smul_eq_mul, map_mul]`. Rewrite `this` using `[add_zero]`. Then use the resulting hypothesis.

Establish `h4` using `valGe_mul ((valGe_emb w a _).2 ha) h3`. Rewrite `h1` using `[map_smul, smul_eq_mul]`. Rewrite `h4` using `[← map_mul, add_zero, h1, valGe_emb]`. Establish `h5 : (D.what₂.places.ramIdx w : ℝ) * s ≤ 0` using `by simpa [vAdd] using h4`. Assume the negation of the conclusion as `hs`.

Use polynomial arithmetic with `[not_le.1 hs]`.
-/
theorem le_zero_of_functional {V : Type} [AddCommGroup V] [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V]
    (Λ : Submodule (𝓞 D.what₂.LL) V) (l : V →ₗ[D.what₂.LL] D.what₂.LL)
    (hl : ∀ x ∈ Λ, ∃ c : 𝓞 D.what₂.LL, l x = (c : D.what₂.LL)) (w : D.what₂.places.Pl) {a : D.what₂.LL} {x : V}
    (hx : x ∈ locW D.what₂.places w Λ) (h1 : l (a • x) = 1) {s : ℝ}
    (ha : a = 0 ∨ (D.what₂.places.ramIdx w : ℝ) * s ≤ (vAdd (D.plEq w) a : ℝ)) : s ≤ 0 := by
  have he : (0 : ℝ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h3 : ValGe D w (D.what₂.embLL (l x)) 0 := by
    clear h1
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := hl x hx
      rw [hc]; exact valGe_of_int w c
    | zero => exact ⟨0, by simp, Or.inl rfl⟩
    | add x y _ _ hx hy =>
      rw [map_add, map_add]; exact valGe_add hx hy
    | smul b x _ hx =>
      have := valGe_mul (valGe_of_mem_intW b) hx
      rw [show b • x = (b : D.what₂.LL) • x from rfl, map_smul, smul_eq_mul, map_mul]
      rwa [add_zero] at this
  have h4 := valGe_mul ((valGe_emb w a _).2 ha) h3
  rw [map_smul, smul_eq_mul] at h1
  rw [← map_mul, add_zero, h1, valGe_emb] at h4
  have h5 : (D.what₂.places.ramIdx w : ℝ) * s ≤ 0 := by simpa [vAdd] using h4
  by_contra hs
  nlinarith [not_le.1 hs]

end General

section Family

open Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ

abbrev oneCls (n : ℕ) (hn : 0 < n) : ClsPkg where
  cls := fun _ => Unit
  clsFin := fun _ => inferInstance
  stab := fun _ _ => PUnit
  stabGrp := fun _ _ => inferInstance
  stabFin := fun _ _ => inferInstance
  DGam := n
  DGam_pos := hn
  dvd := fun _ _ => by simp

def linePer (z : ℂ) : FK Unit →ₗ[ℂ] En 1 →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun ψ F => z * ψ () () * F 0) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring)

/- English proof (translation)
Establish `: ∀ m, Formalism.ThetaLiftIndependence.chainOpM (chainN hc (oneCls n hn)).wt (chainN hc (oneCls n hn)).Kmap m φ = φ`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih`.

Use function extensionality and compare the values at `c y`. Simplify using `[Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, ColumnChain.Kmap, ColumnChain.divDe, ColumnChain.sharp, mulFun, ColumnChain.wt]`. Conclude with `this _`.
-/
theorem col_one {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (n : ℕ) (hn : 0 < n) (φ : FK Unit) :
    (chainN hc (oneCls n hn)).col φ = φ := by
  have : ∀ m, Formalism.ThetaLiftIndependence.chainOpM (chainN hc (oneCls n hn)).wt (chainN hc (oneCls n hn)).Kmap m φ = φ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      funext c y
      simp [Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, ColumnChain.Kmap, ColumnChain.divDe, ColumnChain.sharp, mulFun,
        ColumnChain.wt]
  exact this _

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (nG : ℕ) (hnG : 0 < nG)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW (fun _ => oneCls nG hnG) T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW (fun _ => oneCls nG hnG) T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ (_ : W) i, Unit → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (z : ℂ)
  (NuL : ∀ _ : W, Submodule (𝓞 H.E) (Unit → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((oneCls nG hnG).cls 0))

local notation "DR" => (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol (fun _ => oneCls nG hnG) T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw 1 1 1 le_rfl Unit (fun _ => ()) (fun _ => ()) Lb hT2 (fun _ _ => linePer z) NuL gat hgat)

/- English proof (translation)
Use `show linePer z ((chainN (hcW u) (oneCls nG hnG)).col (eE _ (jE H.φ₀ φ))) F = _`. Rewrite using `[col_one, eE_jE]`. Both sides reduce to the same expression.
-/
theorem fam_per (u : W) (φ : Unit → H.E) (F : En 1) :
    (DR).what₂.perCol u (DR).what₂.mu0 ((DR).jN u φ) F = z * H.φ₀ (φ ()) * F 0 := by
  show linePer z ((chainN (hcW u) (oneCls nG hnG)).col (eE _ (jE H.φ₀ φ))) F = _
  rw [col_one, eE_jE]
  rfl

/- English proof (translation)
Use `show (∃ c : En 1 → 𝓞 H.E, F = ∑ v ∈ genB (eb 1), H.φ₀ (c v : H.E) • v) ↔ _`. Establish `hg : genB (eb 1) = {eb 1 0}`. Use extensionality with `v`. Simplify using `[genB, eq_comm]`. Rewrite using `[hg]`.

Simplify using `only [Finset.sum_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨c (eb 1 0), by rw [hc]; simp⟩`. Introduce and unpack `⟨c, hc⟩`.

Use `⟨fun _ => c, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Rewrite using `[Subsingleton.elim i 0, hc]`. Simplify using the standard rewrite rules.
-/
theorem fam_Mt (F : En 1) : F ∈ ((DR).what₂.Mtilde (DR).what₂.mu0).carrier ↔ ∃ c : 𝓞 H.E, F 0 = H.φ₀ (c : H.E) := by
  show (∃ c : En 1 → 𝓞 H.E, F = ∑ v ∈ genB (eb 1), H.φ₀ (c v : H.E) • v) ↔ _
  have hg : genB (eb 1) = {eb 1 0} := by
    ext v; simp [genB, eq_comm]
  rw [hg]
  simp only [Finset.sum_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c (eb 1 0), by rw [hc]; simp⟩
  · rintro ⟨c, hc⟩
    refine ⟨fun _ => c, ?_⟩
    ext i
    rw [Subsingleton.elim i 0, hc]; simp

/- English proof (translation)
Use `show x ∈ Submodule.span (𝓞 K) (Set.range (Pi.basisFun K Unit)) ↔ _`. Rewrite using `[Set.range_unique, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨a, by simp [Algebra.smul_def]⟩`.

Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨c, by funext i; cases i; simp [Algebra.smul_def, hc]⟩`.
-/
theorem mem_std (K : Type) [Field K] [NumberField K] [StarRing K] (x : Unit → K) :
    x ∈ (stdHLat K Unit).L ↔ ∃ c : 𝓞 K, x () = (c : K) := by
  show x ∈ Submodule.span (𝓞 K) (Set.range (Pi.basisFun K Unit)) ↔ _
  rw [Set.range_unique, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp [Algebra.smul_def]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by funext i; cases i; simp [Algebra.smul_def, hc]⟩

/- English proof (translation)
Use `letI : StarRing H.E := H.cmStar`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `h (fun _ => 1) ((mem_std H.E _).2 ⟨1, rfl⟩) (eb 1 0) ((fam_Mt H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat _).2 ⟨1, by sim …` as an intermediate fact. Establish `e` using `fam_per H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat u (fun _ => 1) (eb 1 0)`.

Establish `e' : z * H.φ₀ ((fun _ => 1 : Unit → H.E) ()) * (eb 1 0 : En 1) 0 = z` using `by simp`. Conclude with `(congrArg (fun t => ValGe DR w t s) (e.trans e')).mp this`. Introduce `h φ hφ F hF`. Take `⟨a, ha⟩` from `(mem_std H.E φ).1 hφ`. Take `⟨c, hc⟩` from `(fam_Mt H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat F).1 hF`.

Establish `e` using `fam_per H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat u φ F`. Rewrite `e` using `[ha, hc]`. Establish `h1` using `valGe_mul (valGe_mul h (valGe_of_int (D := DR) w a)) (valGe_of_int (D := DR) w c)`. Rewrite `h1` using `[add_zero, add_zero]`. Conclude with `(congrArg (fun t => ValGe DR w t s) e).mpr h1`.
-/
theorem fam_perGeOn (u : W) (w : (DR).what₂.places.Pl) (s : ℝ) :
    PerGeOn DR u (DV.MramL DR u) w s ↔ ValGe DR w z s := by
  letI : StarRing H.E := H.cmStar
  constructor
  · intro h
    have := h (fun _ => 1) ((mem_std H.E _).2 ⟨1, rfl⟩) (eb 1 0) ((fam_Mt H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat _).2 ⟨1, by simp⟩)
    have e := fam_per H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat u (fun _ => 1) (eb 1 0)
    have e' : z * H.φ₀ ((fun _ => 1 : Unit → H.E) ()) * (eb 1 0 : En 1) 0 = z := by simp
    exact (congrArg (fun t => ValGe DR w t s) (e.trans e')).mp this
  · intro h φ hφ F hF
    obtain ⟨a, ha⟩ := (mem_std H.E φ).1 hφ
    obtain ⟨c, hc⟩ := (fam_Mt H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat F).1 hF
    have e := fam_per H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat u φ F
    rw [ha, hc] at e
    have h1 := valGe_mul (valGe_mul h (valGe_of_int (D := DR) w a)) (valGe_of_int (D := DR) w c)
    rw [add_zero, add_zero] at h1
    exact (congrArg (fun t => ValGe DR w t s) e).mpr h1

/- English proof (translation)
Establish `h : ((DR).fm u).PRat` using `fun x => ⟨x, rfl⟩`. Use `⟨h, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: ((DR).fm u).PtL h x = x` using `((DR).fm u).ptEmb_inj (((DR).fm u).PtL_spec h x)`. Rewrite using `[this]`. Conclude with `hx`.
-/
theorem fam_ptInt (u : W) : PtInt DR u := by
  have h : ((DR).fm u).PRat := fun x => ⟨x, rfl⟩
  refine ⟨h, fun x hx => ?_⟩
  have : ((DR).fm u).PtL h x = x := ((DR).fm u).ptEmb_inj (((DR).fm u).PtL_spec h x)
  rw [this]
  exact hx

/- English proof (translation)
Use `letI : StarRing H.E := H.cmStar`. Establish `e : ∀ (x : Unit → H.E) (F : En 1), ((DR).mem u).P.period (((DR).fm u).ptEmb x) (((DR).eMt u).symm F) = z * H.φ₀ (x ()) * F 0` using `fun _ _ => rfl`. Prove the components needed by the constructor for the conclusion. Introduce `h w`. Take `⟨y, hy, hv⟩` from `h (fun _ => 1) ((mem_std H.E _).2 ⟨1, rfl⟩) (eb 1 0) ((fam_Mt H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat _).2 ⟨1, by sim …`.

Establish `e' : z * H.φ₀ ((fun _ => 1 : Unit → H.E) ()) * (eb 1 0 : En 1) 0 = z` using `by simp`. Conclude with `⟨y, hy.trans ((e _ _).trans e'), hv w⟩`. Introduce `h x hx F hF`. Take `⟨a, ha⟩` from `(mem_std H.E x).1 hx`. Take `⟨c, hc⟩` from `(fam_Mt H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat F).1 hF`.

Establish `e1` using `e x F`. Rewrite `e1` using `[ha, hc]`. Establish `h1` using `fun w => valGe_mul (valGe_mul (h w) (valGe_of_int (D := DR) w a)) (valGe_of_int (D := DR) w c)`. Take `⟨w0⟩` from `nonempty_place (D := DR)`. Take `⟨y, hy, -⟩` from `h1 w0`.

Use `⟨y, hy.trans e1.symm, fun w => ?_⟩` and prove the remaining obligations. Establish `h2` using `h1 w`. Rewrite `h2` using `[← hy, valGe_emb]`. Simplify using `using h2`.
-/
theorem fam_periodInt (u : W) : PeriodInt DR u ↔
    ∀ w : (DR).what₂.places.Pl, ValGe DR w z (-(((DR).what₂.places.ramIdx w : ℝ) * vGam DR u w)) := by
  letI : StarRing H.E := H.cmStar
  have e : ∀ (x : Unit → H.E) (F : En 1), ((DR).mem u).P.period (((DR).fm u).ptEmb x) (((DR).eMt u).symm F) =
      z * H.φ₀ (x ()) * F 0 := fun _ _ => rfl
  constructor
  · intro h w
    obtain ⟨y, hy, hv⟩ := h (fun _ => 1) ((mem_std H.E _).2 ⟨1, rfl⟩) (eb 1 0) ((fam_Mt H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat _).2 ⟨1, by simp⟩)
    have e' : z * H.φ₀ ((fun _ => 1 : Unit → H.E) ()) * (eb 1 0 : En 1) 0 = z := by simp
    exact ⟨y, hy.trans ((e _ _).trans e'), hv w⟩
  · intro h x hx F hF
    obtain ⟨a, ha⟩ := (mem_std H.E x).1 hx
    obtain ⟨c, hc⟩ := (fam_Mt H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol nG hnG T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw Lb hT2 z NuL gat hgat F).1 hF
    have e1 := e x F
    rw [ha, hc] at e1
    have h1 := fun w => valGe_mul (valGe_mul (h w) (valGe_of_int (D := DR) w a)) (valGe_of_int (D := DR) w c)
    obtain ⟨w0⟩ := nonempty_place (D := DR)
    obtain ⟨y, hy, -⟩ := h1 w0
    refine ⟨y, hy.trans e1.symm, fun w => ?_⟩
    have h2 := h1 w
    rw [← hy, valGe_emb] at h2
    simpa using h2

/- English proof (translation)
Use `letI : StarRing H.E := H.cmStar`. Establish `he : (0 : ℝ) < (DR).what₂.places.ramIdx w` using `by exact_mod_cast (DR).what₂.places.ramIdx_pos w`. Establish `hcol : ∀ x : Unit → H.E, ((DR).mem u).C.col (((DR).fm u).emb 0 x) = ((DR).fm u).emb (DR).R.m x` using `fun x => col_one (hcW u) nG hnG _`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨y, hy, a, x, hx, rfl, ha⟩` from `h (fun _ => 1) ((mem_std H.E _).2 ⟨1, rfl⟩)`. Establish `h1 : a • x = (fun _ => 1 : Unit → H.E)` using `((DR).fm u).emb_inj _ (hy.trans (hcol _))`. Conclude with `le_zero_of_functional (D := DR) (V := (((DR).fm u).lat (DR).R.m).V) _ (LinearMap.proj (R := H.E) (φ := fun _ : Unit => H.E) ()) (fun x hx => (mem_std H.E x).1 hx) w hx (congrFun h1 ()) ha`. Introduce `hs φ hφ`. Use `⟨φ, (hcol φ).symm, 1, φ, Submodule.subset_span hφ, (one_smul _ _).symm, Or.inr ?_⟩` and prove the remaining obligations.

Establish `: vAdd ((DR).plEq w) (1 : (DR).what₂.LL) = 0` using `by simp [vAdd]`. Rewrite using `[this]`. Simplify using `using mul_nonpos_of_nonneg_of_nonpos he.le hs`.
-/
theorem fam_colGeOn (u : W) (w : (DR).what₂.places.Pl) (s : ℝ) : ColGeOn DR u (DV.MramL DR u) w s ↔ s ≤ 0 := by
  letI : StarRing H.E := H.cmStar
  have he : (0 : ℝ) < (DR).what₂.places.ramIdx w := by exact_mod_cast (DR).what₂.places.ramIdx_pos w
  have hcol : ∀ x : Unit → H.E, ((DR).mem u).C.col (((DR).fm u).emb 0 x) = ((DR).fm u).emb (DR).R.m x :=
    fun x => col_one (hcW u) nG hnG _
  constructor
  · intro h
    obtain ⟨y, hy, a, x, hx, rfl, ha⟩ := h (fun _ => 1) ((mem_std H.E _).2 ⟨1, rfl⟩)
    have h1 : a • x = (fun _ => 1 : Unit → H.E) := ((DR).fm u).emb_inj _ (hy.trans (hcol _))
    exact le_zero_of_functional (D := DR) (V := (((DR).fm u).lat (DR).R.m).V) _ (LinearMap.proj (R := H.E) (φ := fun _ : Unit => H.E) ())
      (fun x hx => (mem_std H.E x).1 hx) w hx (congrFun h1 ()) ha
  · intro hs φ hφ
    refine ⟨φ, (hcol φ).symm, 1, φ, Submodule.subset_span hφ, (one_smul _ _).symm, Or.inr ?_⟩
    have : vAdd ((DR).plEq w) (1 : (DR).what₂.LL) = 0 := by simp [vAdd]
    rw [this]
    simpa using mul_nonpos_of_nonneg_of_nonpos he.le hs

end Family

end GlobalTheory.Core.Int.Model
