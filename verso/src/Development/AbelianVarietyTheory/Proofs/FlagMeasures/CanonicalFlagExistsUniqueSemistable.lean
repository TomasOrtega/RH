import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTrivialPointwise

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.PointFlag

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
  (X : InfinitePlace K → Matrix ι ι ℂ)

omit [IsTotallyComplex K] in

/- English proof (translation)
Establish `mono : ∀ {A B : Submodule (𝓞 K) V}, A ≤ B → zl (Formalism.HermitianLatticesTheory.realize b X) A ≤ zl (Formalism.HermitianLatticesTheory.realize b X) B`. Introduce and unpack `A B hAB y ⟨z, hz, rfl⟩`. Conclude with `⟨z, hAB hz, rfl⟩`. Conclude with `⟨h, mono h, fun y hy hy' => hS.2.2 y (mono hA hy) hy'⟩`.
-/
theorem isSat_of_le {L A S : Submodule (𝓞 K) V} (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S) (h : S ≤ A)
    (hA : A ≤ L) : IsSat (Formalism.HermitianLatticesTheory.realize b X) A S := by
  have mono : ∀ {A B : Submodule (𝓞 K) V}, A ≤ B →
      zl (Formalism.HermitianLatticesTheory.realize b X) A ≤ zl (Formalism.HermitianLatticesTheory.realize b X) B := by
    rintro A B hAB y ⟨z, hz, rfl⟩
    exact ⟨z, hAB hz, rfl⟩
  exact ⟨h, mono h, fun y hy hy' => hS.2.2 y (mono hA hy) hy'⟩

omit [IsTotallyComplex K] in

/- English proof (translation)
Establish `hSB` using `satBasic (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A (plLat K V ι b X hX A hA).1`. Use `lt_of_le_of_ne (hSB.2.2.2.2.2.2.2 S hS).2.1 (fun h => hne ?_)` and prove the remaining obligations. Conclude with `(hSB.2.2.1 S A hS hS.1 le_rfl h.symm).symm`.
-/
theorem rk_lt (hX : ∀ v, IsUnit (X v).det) {A S : Submodule (𝓞 K) V} (hA : A.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) A S) (hne : S ≠ A) :
    rk (Formalism.HermitianLatticesTheory.realize b X) S < rk (Formalism.HermitianLatticesTheory.realize b X) A := by
  have hSB := satBasic (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A (plLat K V ι b X hX A hA).1
  refine lt_of_le_of_ne (hSB.2.2.2.2.2.2.2 S hS).2.1 (fun h => hne ?_)
  exact (hSB.2.2.1 S A hS hS.1 le_rfl h.symm).symm

omit [IsTotallyComplex K] in
/- English proof (translation)
Establish `h` using `rk_lt b X hX hA hS hne`. Rewrite `h` using `[(plLat K V ι b X hX A hA).2.1, (plLat K V ι b X hX S (hA.of_le hS.1)).2.1]`. Conclude with `lt_of_mul_lt_mul_left h (Nat.zero_le _)`.
-/
theorem rkK_lt (hX : ∀ v, IsUnit (X v).det) {A S : Submodule (𝓞 K) V} (hA : A.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) A S) (hne : S ≠ A) : rkK S < rkK A := by
  have h := rk_lt b X hX hA hS hne
  rw [(plLat K V ι b X hX A hA).2.1, (plLat K V ι b X hX S (hA.of_le hS.1)).2.1] at h
  exact lt_of_mul_lt_mul_left h (Nat.zero_le _)

omit [IsTotallyComplex K] in
/- English proof (translation)
The claim follows from `(satBasic (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A (plLat K V ι b X hX A hA).1).2.2.2.2.2.1`.
-/
theorem isSat_bot (hX : ∀ v, IsUnit (X v).det) {A : Submodule (𝓞 K) V} (hA : A.FG) :
    IsSat (Formalism.HermitianLatticesTheory.realize b X) A (⊥ : Submodule (𝓞 K) V) :=
  (satBasic (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A (plLat K V ι b X hX A hA).1).2.2.2.2.2.1

/- English proof (translation)
Rewrite using `[(sizeMu K V ι b X hX A hA h0).2.2.2.2.1]`. Conclude with `Real.exp_pos _`.
-/
theorem largestSize_pos (hX : ∀ v, IsUnit (X v).det) {A : Submodule (𝓞 K) V} (hA : A.FG) (h0 : A ≠ ⊥) :
    0 < largestSize b X A := by
  rw [(sizeMu K V ι b X hX A hA h0).2.2.2.2.1]
  exact Real.exp_pos _

/- English proof (translation)
Establish `h0 : A ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `hne (le_bot_iff.1 hS.1)`. Establish `hlat` using `(plLat K V ι b X hX A hA).1`. Take `⟨-, -, hsQ, -, hlarge, -⟩` from `sizeMu K V ι b X hX A hA h0`.

Use `set ρ := Formalism.HermitianLatticesTheory.realize b X`. Establish `hq` using `(satBasic (𝓞 K) V _ ρ A hlat).2.2.2.2.2.2.2 S hS`. Establish `hlt : rk ρ S < rk ρ A` using `rk_lt b X hX hA hS hne`. Establish `hmin` using `((muChar (𝓞 K) V _ ρ A hlat h0).2.1 (muMin ρ A)).1 le_rfl S hS.1`. Establish `hslQ : muMin ρ A ≤ Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ S))`.

Establish `hr : (Formalism.F.rk (Formalism.F.quot (zl ρ A) (zl ρ S)) : ℝ) = (rk ρ A : ℝ) - rk ρ S`. Rewrite using `[hq.1, Nat.cast_sub hq.2.1]`. Establish `hrpos : (0 : ℝ) < (rk ρ A : ℝ) - rk ρ S`. Establish `: (rk ρ S : ℝ) < rk ρ A` using `by exact_mod_cast hlt`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `Formalism.F.slope`. Rewrite using `[hr, le_div_iff₀ hrpos, hq.2.2]`. Conclude with `hmin`. Rewrite using `[hlarge, hsQ S hS hne]`. Conclude with `Real.exp_le_exp.2 (by linarith)`.
-/
theorem sizeQ_le_largestSize (hX : ∀ v, IsUnit (X v).det) {A S : Submodule (𝓞 K) V} (hA : A.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) A S) (hne : S ≠ A) : sizeQ b X A S ≤ largestSize b X A := by
  have h0 : A ≠ ⊥ := by
    rintro rfl
    exact hne (le_bot_iff.1 hS.1)
  have hlat := (plLat K V ι b X hX A hA).1
  obtain ⟨-, -, hsQ, -, hlarge, -⟩ := sizeMu K V ι b X hX A hA h0
  set ρ := Formalism.HermitianLatticesTheory.realize b X
  have hq := (satBasic (𝓞 K) V _ ρ A hlat).2.2.2.2.2.2.2 S hS
  have hlt : rk ρ S < rk ρ A := rk_lt b X hX hA hS hne
  have hmin := ((muChar (𝓞 K) V _ ρ A hlat h0).2.1 (muMin ρ A)).1 le_rfl S hS.1
  have hslQ : muMin ρ A ≤ Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ S)) := by
    have hr : (Formalism.F.rk (Formalism.F.quot (zl ρ A) (zl ρ S)) : ℝ) = (rk ρ A : ℝ) - rk ρ S := by
      rw [hq.1, Nat.cast_sub hq.2.1]
    have hrpos : (0 : ℝ) < (rk ρ A : ℝ) - rk ρ S := by
      have : (rk ρ S : ℝ) < rk ρ A := by exact_mod_cast hlt
      linarith
    unfold Formalism.F.slope
    rw [hr, le_div_iff₀ hrpos, hq.2.2]
    exact hmin
  rw [hlarge, hsQ S hS hne]
  exact Real.exp_le_exp.2 (by linarith)

end General

variable (I : AutInst) (x : I.GA)

/- English proof (translation)
The claim follows from `(GlobalTheory.NearLowerCompare.lamX_isLattice I x).fg.of_le h`.
-/
theorem fg_of_le {N : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : N ≤ lamX I x) : N.FG :=
  (GlobalTheory.NearLowerCompare.lamX_isLattice I x).fg.of_le h

/- English proof (translation)
The claim follows from `GlobalTheory.NearLowerCompare.frm_isUnit I x`.
-/
theorem frm_unit : ∀ w, IsUnit (frm I x w).det := GlobalTheory.NearLowerCompare.frm_isUnit I x

/- English proof (translation)
The claim follows from `sSup_le fun _ h => h.1`.
-/
theorem stepLe_le (t : ℝ) : stepLe I x t ≤ lamX I x := sSup_le fun _ h => h.1

/- English proof (translation)
The claim follows from `sSup_le fun _ h => h.1`.
-/
theorem stepLt_le (t : ℝ) : stepLt I x t ≤ lamX I x := sSup_le fun _ h => h.1

/- English proof (translation)
The claim follows from `sSup_le_sSup fun _ hN => ⟨hN.1, hN.2.1, hN.2.2.trans h⟩`.
-/
theorem stepLe_mono {s t : ℝ} (h : s ≤ t) : stepLe I x s ≤ stepLe I x t :=
  sSup_le_sSup fun _ hN => ⟨hN.1, hN.2.1, hN.2.2.trans h⟩

/- English proof (translation)
The claim follows from `sSup_le_sSup fun _ hN => ⟨hN.1, hN.2.1, hN.2.2.trans_lt h⟩`.
-/
theorem stepLe_le_stepLt {s t : ℝ} (h : s < t) : stepLe I x s ≤ stepLt I x t :=
  sSup_le_sSup fun _ hN => ⟨hN.1, hN.2.1, hN.2.2.trans_lt h⟩

/- English proof (translation)
The claim follows from `sSup_le_sSup fun _ hN => ⟨hN.1, hN.2.1, hN.2.2.le⟩`.
-/
theorem stepLt_le_stepLe (t : ℝ) : stepLt I x t ≤ stepLe I x t :=
  sSup_le_sSup fun _ hN => ⟨hN.1, hN.2.1, hN.2.2.le⟩

/- English proof (translation)
Establish `: IsTotallyComplex I.E` using `I.cm.cmUnram.1`. Conclude with `largestSize_pos _ _ (frm_unit I x) (fg_of_le I x h) h0`.
-/
theorem large_pos {N : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : N ≤ lamX I x) (h0 : N ≠ ⊥) :
    0 < largestSize (bas I) (frm I x) N := by
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  exact largestSize_pos _ _ (frm_unit I x) (fg_of_le I x h) h0

/- English proof (translation)
Establish `: IsTotallyComplex I.E` using `I.cm.cmUnram.1`. Conclude with `sizeQ_le_largestSize _ _ (frm_unit I x) (fg_of_le I x h) hS hne`.
-/
theorem sizeQ_le {A S : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : A ≤ lamX I x)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A S) (hne : S ≠ A) :
    sizeQ (bas I) (frm I x) A S ≤ largestSize (bas I) (frm I x) A := by
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  exact sizeQ_le_largestSize _ _ (frm_unit I x) (fg_of_le I x h) hS hne

/- English proof (translation)
Unfold `stepLe`. Rewrite using `[sSup_eq_bot]`. Introduce and unpack `N ⟨h1, h2, h3⟩`. Conclude with `absurd (large_pos I x h1 h2) (not_lt.2 (h3.trans ht))`.
-/
theorem stepLe_nonpos {t : ℝ} (ht : t ≤ 0) : stepLe I x t = ⊥ := by
  unfold stepLe
  rw [sSup_eq_bot]
  rintro N ⟨h1, h2, h3⟩
  exact absurd (large_pos I x h1 h2) (not_lt.2 (h3.trans ht))

def IsJump (t : ℝ) : Prop := 0 < t ∧ stepLt I x t < stepLe I x t

/- English proof (translation)
Establish `hs : 0 < s` using `h ▸ large_pos I x (stepLe_le I x s) h0`. Use `⟨hs, lt_of_le_of_ne (stepLt_le_stepLe I x s) fun e => ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.T.canonicalLatticeFiltration_size_properties I x s hs).2.2.2.2.2.1 (e ▸ h0)` as an intermediate fact. Rewrite `this` using `[e, h]`. Conclude with `lt_irrefl _ this`.
-/
theorem isJump_of_large {s : ℝ} (h0 : stepLe I x s ≠ ⊥)
    (h : largestSize (bas I) (frm I x) (stepLe I x s) = s) : IsJump I x s := by
  have hs : 0 < s := h ▸ large_pos I x (stepLe_le I x s) h0
  refine ⟨hs, lt_of_le_of_ne (stepLt_le_stepLe I x s) fun e => ?_⟩
  have := (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x s hs).2.2.2.2.2.1 (e ▸ h0)
  rw [e, h] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `h0 : stepLe I x t ≠ ⊥` using `ne_bot_of_gt h.2`. Use `le_antisymm ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t h.1).2.2.2.2.1 h0) (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Conclude with `h.2.not_ge (le_sSup ⟨stepLe_le I x t, h0, hlt⟩)`.
-/
theorem IsJump.large {t : ℝ} (h : IsJump I x t) : largestSize (bas I) (frm I x) (stepLe I x t) = t := by
  have h0 : stepLe I x t ≠ ⊥ := ne_bot_of_gt h.2
  refine le_antisymm ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t h.1).2.2.2.2.1 h0) (not_lt.1 fun hlt => ?_)
  exact h.2.not_ge (le_sSup ⟨stepLe_le I x t, h0, hlt⟩)

/- English proof (translation)
Establish `H` using `GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t h.1`. Use `le_antisymm ?_ (H.2.2.2.2.2.2.2.1 _ h.2 (stepLe_le I x t))` and prove the remaining obligations. Conclude with `(sizeQ_le I x (stepLe_le I x t) (isSat_of_le _ _ H.2.1 h.2.le (stepLe_le I x t)) h.2.ne).trans (h.large I x).le`.
-/
theorem IsJump.sizeQ_eq {t : ℝ} (h : IsJump I x t) :
    sizeQ (bas I) (frm I x) (stepLe I x t) (stepLt I x t) = t := by
  have H := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t h.1
  refine le_antisymm ?_ (H.2.2.2.2.2.2.2.1 _ h.2 (stepLe_le I x t))
  exact (sizeQ_le I x (stepLe_le I x t) (isSat_of_le _ _ H.2.1 h.2.le (stepLe_le I x t)) h.2.ne).trans
    (h.large I x).le

/- English proof (translation)
The claim follows from `GlobalTheory.PointFlag.rkK_lt _ _ (frm_unit I x) (fg_of_le I x (stepLe_le I x t)) (isSat_of_le _ _ (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t h.1).2.1 h.2.le (stepLe_le I x t)) h.2.ne`.
-/
theorem IsJump.rkK_lt {t : ℝ} (h : IsJump I x t) : rkK (stepLt I x t) < rkK (stepLe I x t) :=
  GlobalTheory.PointFlag.rkK_lt _ _ (frm_unit I x) (fg_of_le I x (stepLe_le I x t))
    (isSat_of_le _ _ (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t h.1).2.1 h.2.le (stepLe_le I x t)) h.2.ne

/- English proof (translation)
Establish `ht : 0 < t` using `not_le.1 fun h => h0 (stepLe_nonpos I x h)`. Establish `hle` using `(GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht).2.2.2.2.1 h0`. Establish `e : stepLe I x (largestSize (bas I) (frm I x) (stepLe I x t)) = stepLe I x t` using `le_antisymm (stepLe_mono I x hle) (le_sSup ⟨stepLe_le I x t, h0, le_rfl⟩)`. Conclude with `⟨_, hle, isJump_of_large I x (e.symm ▸ h0) (by rw [e]), e⟩`.
-/
theorem exists_jump_le {t : ℝ} (h0 : stepLe I x t ≠ ⊥) :
    ∃ s, s ≤ t ∧ IsJump I x s ∧ stepLe I x s = stepLe I x t := by
  have ht : 0 < t := not_le.1 fun h => h0 (stepLe_nonpos I x h)
  have hle := (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht).2.2.2.2.1 h0
  have e : stepLe I x (largestSize (bas I) (frm I x) (stepLe I x t)) = stepLe I x t :=
    le_antisymm (stepLe_mono I x hle) (le_sSup ⟨stepLe_le I x t, h0, le_rfl⟩)
  exact ⟨_, hle, isJump_of_large I x (e.symm ▸ h0) (by rw [e]), e⟩

/- English proof (translation)
Establish `hle` using `(GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht).2.2.2.2.2.1 h0`. Establish `e : stepLe I x (largestSize (bas I) (frm I x) (stepLt I x t)) = stepLt I x t` using `le_antisymm (stepLe_le_stepLt I x hle) (le_sSup ⟨stepLt_le I x t, h0, le_rfl⟩)`. Conclude with `⟨_, hle, isJump_of_large I x (e.symm ▸ h0) (by rw [e]), e⟩`.
-/
theorem exists_jump_lt {t : ℝ} (ht : 0 < t) (h0 : stepLt I x t ≠ ⊥) :
    ∃ s, s < t ∧ IsJump I x s ∧ stepLe I x s = stepLt I x t := by
  have hle := (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht).2.2.2.2.2.1 h0
  have e : stepLe I x (largestSize (bas I) (frm I x) (stepLt I x t)) = stepLt I x t :=
    le_antisymm (stepLe_le_stepLt I x hle) (le_sSup ⟨stepLt_le I x t, h0, le_rfl⟩)
  exact ⟨_, hle, isJump_of_large I x (e.symm ▸ h0) (by rw [e]), e⟩

/- English proof (translation)
The claim follows from `Submodule.finrank_mono (Submodule.span_mono h)`.
-/
theorem rkK_mono {A B : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : A ≤ B) : rkK A ≤ rkK B :=
  Submodule.finrank_mono (Submodule.span_mono h)

/- English proof (translation)
Use `Set.Finite.of_finite_image (f := fun t => rkK (stepLe I x t)) ((Set.finite_Iic (Module.finrank I.E (Fin I.n → I.E))).subset ?_) (StrictMonoOn.injOn ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨t, -, rfl⟩`. Conclude with `Submodule.finrank_le _`. Introduce `s _ t ht hst`. Conclude with `(rkK_mono I (stepLe_le_stepLt I x hst)).trans_lt (ht.1.rkK_lt I x)`.
-/
theorem finite_jumps : {t | IsJump I x t ∧ t < 1 / 2}.Finite := by
  refine Set.Finite.of_finite_image (f := fun t => rkK (stepLe I x t))
    ((Set.finite_Iic (Module.finrank I.E (Fin I.n → I.E))).subset ?_) (StrictMonoOn.injOn ?_)
  · rintro _ ⟨t, -, rfl⟩
    exact Submodule.finrank_le _
  · intro s _ t ht hst
    exact (rkK_mono I (stepLe_le_stepLt I x hst)).trans_lt (ht.1.rkK_lt I x)

/- English proof (translation)
Use `set J := (finite_jumps I x).toFinset with hJ`. Set `τ : Fin J.card ↪o ℝ` to `J.orderEmbOfFin rfl`. Establish `hτ : ∀ i, IsJump I x (τ i) ∧ τ i < 1 / 2` using `fun i => (finite_jumps I x).mem_toFinset.1 (J.orderEmbOfFin_mem rfl i)`. Establish `hsurj : ∀ s, IsJump I x s → s < 1 / 2 → ∃ i, τ i = s`. Introduce `s h1 h2`.

Establish `: s ∈ Set.range τ`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `(finite_jumps I x).mem_toFinset.2 ⟨h1, h2⟩`. Conclude with `this`. Set `S : Fin (J.card + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)` to `Fin.cons ⊥ fun i => stepLe I x (τ i)`.

Establish `hS0 : S 0 = ⊥` using `rfl`. Establish `hSs : ∀ i, S i.succ = stepLe I x (τ i)` using `fun i => rfl`. Establish `hlow : ∀ (m : Fin (J.card + 1)) (u : ℝ), (∀ k : Fin J.card, k.succ ≤ m → τ k < u) → S m ≤ stepLt I x u`. Introduce `m u h`. Proceed by induction on `m using Fin.cases with`.

Consider the case `zero => exact bot_le`. Consider the case `succ k => exact stepLe_le_stepLt I x (h k le_rfl)`. Establish `hlow' : ∀ i : Fin J.card, S i.castSucc ≤ stepLt I x (τ i)` using `fun i => hlow _ _ fun k hk => τ.strictMono (Fin.succ_le_castSucc_iff.1 hk)`. Establish `hmono : StrictMono S` using `Fin.strictMono_iff_lt_succ.2 fun i => (hlow' i).trans_lt (hτ i).1.2`. Establish `hup : ∀ (m : Fin (J.card + 1)) (u : ℝ), 0 < u → u ≤ 1 / 2 → (∀ k : Fin J.card, τ k < u → k.succ ≤ m) → stepLt I x u ≤ S m`.

Introduce `m u hu hu' h`. Distinguish the cases in `h0 : stepLt I x u = ⊥`. Rewrite using `[h0]`. Conclude with `bot_le`. Take `⟨s, hs, hj, e⟩` from `exists_jump_lt I x hu h0`.

Take `⟨k, rfl⟩` from `hsurj s hj (hs.trans_le hu')`. Rewrite using `[← e, ← hSs]`. Conclude with `hmono.monotone (h k hs)`. Use `⟨J.card, S, τ, hS0, hmono, ?_, τ.strictMono, fun i => ⟨(hτ i).1.1, (hτ i).2, hSs i, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `le_antisymm (hlow _ _ fun k _ => (hτ k).2) (hup _ _ (by norm_num) le_rfl fun k _ => Fin.le_last _)`.

Establish `e : S i.castSucc = stepLt I x (τ i)` using `le_antisymm (hlow' i) (hup _ _ (hτ i).1.1 (hτ i).2.le fun k hk => Fin.succ_le_castSucc_iff.2 (τ.lt_iff_lt.1 hk))`. Rewrite using `[e, hSs]`. Conclude with `(hτ i).1.sizeQ_eq I x`. Introduce `t ht`. Distinguish the cases in `h0 : stepLe I x t = ⊥`.

Conclude with `⟨0, h0.symm⟩`. Take `⟨s, hs, hj, e⟩` from `exists_jump_le I x h0`. Take `⟨k, rfl⟩` from `hsurj s hj (hs.trans_lt ht)`. Conclude with `⟨k.succ, e⟩`.
-/
theorem exists_flag : ∃ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ),
    HasFlag I x S τ := by
  classical
  set J := (finite_jumps I x).toFinset with hJ
  let τ : Fin J.card ↪o ℝ := J.orderEmbOfFin rfl
  have hτ : ∀ i, IsJump I x (τ i) ∧ τ i < 1 / 2 := fun i =>
    (finite_jumps I x).mem_toFinset.1 (J.orderEmbOfFin_mem rfl i)
  have hsurj : ∀ s, IsJump I x s → s < 1 / 2 → ∃ i, τ i = s := by
    intro s h1 h2
    have : s ∈ Set.range τ := by
      rw [Finset.range_orderEmbOfFin]
      exact (finite_jumps I x).mem_toFinset.2 ⟨h1, h2⟩
    exact this
  let S : Fin (J.card + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E) := Fin.cons ⊥ fun i => stepLe I x (τ i)
  have hS0 : S 0 = ⊥ := rfl
  have hSs : ∀ i, S i.succ = stepLe I x (τ i) := fun i => rfl
  have hlow : ∀ (m : Fin (J.card + 1)) (u : ℝ), (∀ k : Fin J.card, k.succ ≤ m → τ k < u) →
      S m ≤ stepLt I x u := by
    intro m u h
    induction m using Fin.cases with
    | zero => exact bot_le
    | succ k => exact stepLe_le_stepLt I x (h k le_rfl)
  have hlow' : ∀ i : Fin J.card, S i.castSucc ≤ stepLt I x (τ i) := fun i =>
    hlow _ _ fun k hk => τ.strictMono (Fin.succ_le_castSucc_iff.1 hk)
  have hmono : StrictMono S := Fin.strictMono_iff_lt_succ.2 fun i => (hlow' i).trans_lt (hτ i).1.2
  have hup : ∀ (m : Fin (J.card + 1)) (u : ℝ), 0 < u → u ≤ 1 / 2 → (∀ k : Fin J.card, τ k < u → k.succ ≤ m) →
      stepLt I x u ≤ S m := by
    intro m u hu hu' h
    by_cases h0 : stepLt I x u = ⊥
    · rw [h0]; exact bot_le
    · obtain ⟨s, hs, hj, e⟩ := exists_jump_lt I x hu h0
      obtain ⟨k, rfl⟩ := hsurj s hj (hs.trans_le hu')
      rw [← e, ← hSs]
      exact hmono.monotone (h k hs)
  refine ⟨J.card, S, τ, hS0, hmono, ?_, τ.strictMono, fun i => ⟨(hτ i).1.1, (hτ i).2, hSs i, ?_⟩, ?_⟩
  · exact le_antisymm (hlow _ _ fun k _ => (hτ k).2)
      (hup _ _ (by norm_num) le_rfl fun k _ => Fin.le_last _)
  · have e : S i.castSucc = stepLt I x (τ i) :=
      le_antisymm (hlow' i) (hup _ _ (hτ i).1.1 (hτ i).2.le fun k hk =>
        Fin.succ_le_castSucc_iff.2 (τ.lt_iff_lt.1 hk))
    rw [e, hSs]
    exact (hτ i).1.sizeQ_eq I x
  · intro t ht
    by_cases h0 : stepLe I x t = ⊥
    · exact ⟨0, h0.symm⟩
    · obtain ⟨s, hs, hj, e⟩ := exists_jump_le I x h0
      obtain ⟨k, rfl⟩ := hsurj s hj (hs.trans_lt ht)
      exact ⟨k.succ, e⟩

variable {I x} {a : ℕ} {S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)} {τ : Fin a → ℝ}

/- English proof (translation)
Take `⟨h0, -, -, -, hi, -⟩` from `h`. Proceed by induction on `m using Fin.cases with`. Consider the case `zero => rw [h0]`. Conclude with `isSat_bot _ _ (frm_unit I x) (fg_of_le I x le_rfl)`. Consider the case `succ k => rw [(hi k).2.2.1]`.

Conclude with `(GlobalTheory.T.canonicalLatticeFiltration_size_properties I x _ (hi k).1).1`.
-/
theorem flag_sat (h : HasFlag I x S τ) (m : Fin (a + 1)) :
    IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S m) := by
  obtain ⟨h0, -, -, -, hi, -⟩ := h
  induction m using Fin.cases with
  | zero => rw [h0]; exact isSat_bot _ _ (frm_unit I x) (fg_of_le I x le_rfl)
  | succ k => rw [(hi k).2.2.1]; exact (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x _ (hi k).1).1

/- English proof (translation)
Establish `hlt : S i.castSucc < S i.succ` using `h.2.1 Fin.castSucc_lt_succ`. Take `⟨h1, -, h3, h4⟩` from `h.2.2.2.2.1 i`. Establish `hle` using `sizeQ_le I x (flag_sat h i.succ).1 (isSat_of_le _ _ (flag_sat h i.castSucc) hlt.le (flag_sat h i.succ).1) hlt.ne`. Rewrite `hle` using `[h4, h3]`. Establish `h0 : stepLe I x (τ i) ≠ ⊥` using `h3 ▸ ne_bot_of_gt hlt`.

Conclude with `isJump_of_large I x h0 (le_antisymm ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x _ h1).2.2.2.2.1 h0) hle)`.
-/
theorem flag_jump (h : HasFlag I x S τ) (i : Fin a) : IsJump I x (τ i) := by
  have hlt : S i.castSucc < S i.succ := h.2.1 Fin.castSucc_lt_succ
  obtain ⟨h1, -, h3, h4⟩ := h.2.2.2.2.1 i
  have hle := sizeQ_le I x (flag_sat h i.succ).1
    (isSat_of_le _ _ (flag_sat h i.castSucc) hlt.le (flag_sat h i.succ).1) hlt.ne
  rw [h4, h3] at hle
  have h0 : stepLe I x (τ i) ≠ ⊥ := h3 ▸ ne_bot_of_gt hlt
  exact isJump_of_large I x h0 (le_antisymm ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x _ h1).2.2.2.2.1 h0) hle)

/- English proof (translation)
Use extensionality with `s`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨flag_jump h i, (h.2.2.2.2.1 i).2.1⟩`. Introduce and unpack `⟨h1, h2⟩`.

Take `⟨m, hm⟩` from `h.2.2.2.2.2 s h2`. Proceed by induction on `m using Fin.cases with`. Consider the case `zero => exact absurd (hm.symm.trans h.1) (ne_bot_of_gt h1.2)`. Consider the case `succ k`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Rewrite using `[← (flag_jump h k).large I x, ← (h.2.2.2.2.1 k).2.2.1, hm, h1.large I x]`.
-/
theorem flag_range (h : HasFlag I x S τ) : Set.range τ = {t | IsJump I x t ∧ t < 1 / 2} := by
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨flag_jump h i, (h.2.2.2.2.1 i).2.1⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨m, hm⟩ := h.2.2.2.2.2 s h2
    induction m using Fin.cases with
    | zero => exact absurd (hm.symm.trans h.1) (ne_bot_of_gt h1.2)
    | succ k =>
      refine ⟨k, ?_⟩
      rw [← (flag_jump h k).large I x, ← (h.2.2.2.2.1 k).2.2.1, hm, h1.large I x]

/- English proof (translation)
Establish `hi` using `h.2.2.2.2.1`. Apply `le_antisymm` to reduce the goal to its premises. Establish `: ∀ m : Fin (a + 1), m ≤ i.castSucc → S m ≤ stepLt I x (τ i)`. Introduce `m hm`. Proceed by induction on `m using Fin.cases with`.

Consider the case `zero => rw [h.1]`. Conclude with `bot_le`. Consider the case `succ k`. Rewrite using `[(hi k).2.2.1]`. Conclude with `stepLe_le_stepLt I x (h.2.2.2.1 (Fin.succ_le_castSucc_iff.1 hm))`.

Conclude with `this _ le_rfl`. Distinguish the cases in `h0 : stepLt I x (τ i) = ⊥`. Rewrite using `[h0]`. Conclude with `bot_le`. Take `⟨s, hs, hj, e⟩` from `exists_jump_lt I x (hi i).1 h0`.

Choose the witnesses or unpack the hypotheses as in `⟨k, rfl⟩ : s ∈ Set.range τ := by`. Rewrite using `[flag_range h]`. Conclude with `⟨hj, hs.trans (hi i).2.1⟩`. Rewrite using `[← e, ← (hi k).2.2.1]`. Conclude with `h.2.1.monotone (Fin.succ_le_castSucc_iff.2 (h.2.2.2.1.lt_iff_lt.1 hs))`.
-/
theorem flag_castSucc (h : HasFlag I x S τ) (i : Fin a) : S i.castSucc = stepLt I x (τ i) := by
  have hi := h.2.2.2.2.1
  apply le_antisymm
  · have : ∀ m : Fin (a + 1), m ≤ i.castSucc → S m ≤ stepLt I x (τ i) := by
      intro m hm
      induction m using Fin.cases with
      | zero => rw [h.1]; exact bot_le
      | succ k =>
        rw [(hi k).2.2.1]
        exact stepLe_le_stepLt I x (h.2.2.2.1 (Fin.succ_le_castSucc_iff.1 hm))
    exact this _ le_rfl
  · by_cases h0 : stepLt I x (τ i) = ⊥
    · rw [h0]; exact bot_le
    · obtain ⟨s, hs, hj, e⟩ := exists_jump_lt I x (hi i).1 h0
      obtain ⟨k, rfl⟩ : s ∈ Set.range τ := by
        rw [flag_range h]; exact ⟨hj, hs.trans (hi i).2.1⟩
      rw [← e, ← (hi k).2.2.1]
      exact h.2.1.monotone (Fin.succ_le_castSucc_iff.2 (h.2.2.2.1.lt_iff_lt.1 hs))

/- English proof (translation)
Take `⟨S, hS, hj⟩` from `h`. Take `⟨S', hS', hj'⟩` from `h'`. Establish `hr : Set.range τ = Set.range τ'` using `(flag_range hS).trans (flag_range hS').symm`. Establish `e : a = a'`. Establish `h1` using `Set.ncard_range_of_injective hS.2.2.2.1.injective`.

Establish `h2` using `Set.ncard_range_of_injective hS'.2.2.2.1.injective`. Rewrite `h1` using `[hr, h2]`. Simplify using `using h1.symm`. Substitute `e` using the available equality. Establish `eτ : τ = τ'` using `(StrictMono.range_inj hS.2.2.2.1 hS'.2.2.2.1).1 hr`.

Substitute `eτ` using the available equality. Use `⟨rfl, fun i => ?_, fun i => rfl⟩` and prove the remaining obligations. Establish `h1` using `hj i`. Establish `h2` using `hj' i`. Rewrite `h1` using `[flag_castSucc hS, (hS.2.2.2.2.1 i).2.2.1]`.

Rewrite `h2` using `[flag_castSucc hS', (hS'.2.2.2.2.1 i).2.2.1]`. Conclude with `Nat.add_left_cancel (h1.symm.trans h2)`.
-/
theorem type_unique {a a' : ℕ} {j : Fin a → ℕ} {τ : Fin a → ℝ} {j' : Fin a' → ℕ} {τ' : Fin a' → ℝ}
    (h : HasType I x j τ) (h' : HasType I x j' τ') :
    ∃ e : a = a', (∀ i, j i = j' (Fin.cast e i)) ∧ ∀ i, τ i = τ' (Fin.cast e i) := by
  obtain ⟨S, hS, hj⟩ := h
  obtain ⟨S', hS', hj'⟩ := h'
  have hr : Set.range τ = Set.range τ' := (flag_range hS).trans (flag_range hS').symm
  have e : a = a' := by
    have h1 := Set.ncard_range_of_injective hS.2.2.2.1.injective
    have h2 := Set.ncard_range_of_injective hS'.2.2.2.1.injective
    rw [hr, h2] at h1
    simpa using h1.symm
  subst e
  have eτ : τ = τ' := (StrictMono.range_inj hS.2.2.2.1 hS'.2.2.2.1).1 hr
  subst eτ
  refine ⟨rfl, fun i => ?_, fun i => rfl⟩
  have h1 := hj i
  have h2 := hj' i
  rw [flag_castSucc hS, (hS.2.2.2.2.1 i).2.2.1] at h1
  rw [flag_castSucc hS', (hS'.2.2.2.2.1 i).2.2.1] at h2
  exact Nat.add_left_cancel (h1.symm.trans h2)

/- English proof (translation)
Introduce `I x`. Use `⟨exists_flag I x, fun a a' j τ j' τ' h h' => type_unique h h', fun a S τ h => ⟨fun i => ?_, fun hn => ⟨?_, ?_⟩⟩⟩` and prove the remaining obligations. Establish `hj` using `flag_jump h i`. Establish `e` using `flag_castSucc h i`. Establish `e'` using `(h.2.2.2.2.1 i).2.2.1`.

Rewrite using `[e, e']`. Use `⟨rfl, hj.rkK_lt I x, hj.large I x, (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x _ hj.1).2.2.2.2.2.2.2.1, fun N _ hN hne => ?_⟩` and prove the remaining obligations. Conclude with `(sizeQ_le I x (stepLe_le I x _) hN hne).trans (hj.large I x).le`. Rewrite using `[← ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn).2.2, ← h.2.2.1, ← h.1, h.2.1.injective.eq_iff, Fin.ext_iff]`. Simplify using the standard rewrite rules.

Introduce `ha`. Establish `hj` using `flag_jump h ⟨0, ha⟩`. Take `⟨-, h1, h2⟩` from `(GlobalTheory.T.canonicalLatticeFiltration_size_properties I x _ hj.1).2.2.2.2.2.2.2.2 hn`. Use `le_antisymm (h2.1 ?_) (not_lt.1 fun hlt => ne_bot_of_gt hj.2 (h1.2 hlt))` and prove the remaining obligations. Rewrite using `[← flag_castSucc h, ← h.1]`.

Both sides reduce to the same expression.
-/
theorem flag_spec : ∀ (I : AutInst) (x : I.GA), (∃ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ) ∧ (∀ (a a' : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (j' : Fin a' → ℕ) (τ' : Fin a' → ℝ), HasType I x j τ → HasType I x j' τ' → ∃ h : a = a', (∀ i, j i = j' (Fin.cast h i)) ∧ ∀ i, τ i = τ' (Fin.cast h i)) ∧ ∀ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i : Fin a, S i.castSucc = stepLt I x (τ i) ∧ rkK (S i.castSucc) < rkK (S i.succ) ∧ largestSize (bas I) (frm I x) (S i.succ) = τ i ∧ (∀ N, S i.castSucc < N → N ≤ lamX I x → τ i ≤ sizeQ (bas I) (frm I x) N (S i.castSucc)) ∧ ∀ N, S i.castSucc ≤ N → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (S i.succ) N → N ≠ S i.succ → sizeQ (bas I) (frm I x) (S i.succ) N ≤ τ i) ∧ (1 ≤ I.n → (a = 0 ↔ 1 / 2 ≤ least I x) ∧ ∀ h : 0 < a, τ ⟨0, h⟩ = least I x) := by
  intro I x
  refine ⟨exists_flag I x, fun a a' j τ j' τ' h h' => type_unique h h', fun a S τ h => ⟨fun i => ?_, fun hn => ⟨?_, ?_⟩⟩⟩
  · have hj := flag_jump h i
    have e := flag_castSucc h i
    have e' := (h.2.2.2.2.1 i).2.2.1
    rw [e, e']
    refine ⟨rfl, hj.rkK_lt I x, hj.large I x, (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x _ hj.1).2.2.2.2.2.2.2.1, fun N _ hN hne => ?_⟩
    exact (sizeQ_le I x (stepLe_le I x _) hN hne).trans (hj.large I x).le
  · rw [← ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn).2.2, ← h.2.2.1, ← h.1,
      h.2.1.injective.eq_iff, Fin.ext_iff]
    simp
  · intro ha
    have hj := flag_jump h ⟨0, ha⟩
    obtain ⟨-, h1, h2⟩ := (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x _ hj.1).2.2.2.2.2.2.2.2 hn
    refine le_antisymm (h2.1 ?_) (not_lt.1 fun hlt => ne_bot_of_gt hj.2 (h1.2 hlt))
    rw [← flag_castSucc h, ← h.1]
    rfl

end GlobalTheory.PointFlag
