import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCoreT
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CmpDSmulLetter

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.NTB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

/- English proof (translation)
Rewrite `hg`, `hh`, the goal using `[W.DelF_def]`. Take `⟨k, hk, hgk⟩` from `hg`. Take `⟨m, hm, hhm⟩` from `hh`. Use `⟨k * m, Nat.mul_pos hk hm, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, pow_mul, hgk, one_pow, one_mul, mul_comm, pow_mul, hhm, one_pow]`.
-/
theorem delF_mul {g h : W.Gam} (hg : g ∈ W.DelF) (hh : h ∈ W.DelF) : g * h ∈ W.DelF := by
  rw [W.DelF_def] at hg hh ⊢
  obtain ⟨k, hk, hgk⟩ := hg
  obtain ⟨m, hm, hhm⟩ := hh
  refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hgk, one_pow, one_mul, mul_comm, pow_mul, hhm, one_pow]

/- English proof (translation)
Rewrite `hg`, the goal using `[W.DelF_def]`. Take `⟨k, hk, hgk⟩` from `hg`. Conclude with `⟨k, hk, by rw [inv_pow, hgk, inv_one]⟩`.
-/
theorem delF_inv {g : W.Gam} (hg : g ∈ W.DelF) : g⁻¹ ∈ W.DelF := by
  rw [W.DelF_def] at hg ⊢
  obtain ⟨k, hk, hgk⟩ := hg
  exact ⟨k, hk, by rw [inv_pow, hgk, inv_one]⟩

/- English proof (translation)
Unfold `Formalism.BasicNotions.LocWach.γA Formalism.BasicNotions.letE Formalism.BasicNotions.letγ`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(W.γ₀ g) (Pi.single (M := fun _ : ZMod n => PowerSeries O) c 1 i) = Pi.single (M := fun _ : ZMod n => PowerSeries O) c 1 i`. Distinguish the cases in `h : i = c`. Substitute `h` using the available equality.

Rewrite using `[Pi.single_eq_same, map_one]`. Rewrite using `[Pi.single_eq_of_ne h, map_zero]`.
-/
theorem γA_letE (g : W.Gam) (c : ZMod n) : W.γA g (letE c) = letE c := by
  unfold Formalism.BasicNotions.LocWach.γA Formalism.BasicNotions.letE Formalism.BasicNotions.letγ
  funext i
  change (W.γ₀ g) (Pi.single (M := fun _ : ZMod n => PowerSeries O) c 1 i) =
    Pi.single (M := fun _ : ZMod n => PowerSeries O) c 1 i
  by_cases h : i = c
  · subst h; rw [Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, map_zero]

/- English proof (translation)
Apply the tactic sequence `rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul] <;> rfl`.
-/
theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul] <;> rfl

/- English proof (translation)
Establish `ha' : ∀ δ ∈ W.DelF, W.γA δ a = a` using `ha`. Establish `hy' : y ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ y = y` using `hy`. Use `show a • y ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (a • y) = a • y`. Use `⟨(W.N T).smul_mem a hy'.1, fun δ hδ => ?_⟩` and prove the remaining obligations. Rewrite using `[γD_smulA W T δ a y, ha' δ hδ, hy'.2 δ hδ]`.
-/
theorem smul_mem_NΔ (T : LocLat G Qp LL O) {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T}
    (hy : y ∈ W.NΔ T) : a • y ∈ W.NΔ T := by
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  have hy' : y ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ y = y := hy
  show a • y ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (a • y) = a • y
  refine ⟨(W.N T).smul_mem a hy'.1, fun δ hδ => ?_⟩
  rw [γD_smulA W T δ a y, ha' δ hδ, hy'.2 δ hδ]

/- English proof (translation)
Rewrite using `[← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]`.
-/
theorem map_smulA {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (a : LetA O n) (x : W.DD T₁) :
    W.map F (a • x) = a • W.map F x := by
  rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]

/- English proof (translation)
Unfold `Formalism.BasicNotions.letE`. Rewrite using `[← Pi.single_mul, one_mul]`.
-/
theorem letE_idem (c : ZMod n) : (letE (O := O) c : LetA O n) * letE c = letE c := by
  unfold Formalism.BasicNotions.letE
  rw [← Pi.single_mul, one_mul]

/- English proof (translation)
Use `show ∀ δ ∈ W.DelF, W.γA δ (letE c) = letE c`. Conclude with `fun δ _ => γA_letE W δ c`.
-/
theorem letE_mem (c : ZMod n) : (letE (O := O) c : LetA O n) ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (letE c) = letE c
  exact fun δ _ => γA_letE W δ c

/- English proof (translation)
Unfold `Formalism.MainNotions.LiftingTheory.CaseA at hcase`. Establish `e` using `(LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hcase.1).finrank_eq`. Rewrite `e` using `[Module.finrank_self]`. Conclude with `e.symm`.
-/
theorem finrank_one (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) : Module.finrank K₀ K = 1 := by
  unfold Formalism.MainNotions.LiftingTheory.CaseA at hcase
  have e := (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hcase.1).finrank_eq
  rw [Module.finrank_self] at e
  exact e.symm

/- English proof (translation)
Unfold `Formalism.MainNotions.DeltaInvariantLattices.P9W at hP9`. Establish `h` using `hP9 T hT`. Unfold `Formalism.MainNotions.DeltaInvariantLattices.p9 at h`. Establish `hf` using `finrank_one W hcase`. Take `⟨h1, _, h3⟩` from `h hcase.2.1 hcase.2.2`.

Rewrite `h1` using `[hf, Nat.div_one]`. Conclude with `⟨h1, (h3 hf).2⟩`.
-/
theorem p9mod_of (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) : W.DelF.card = PD.p - 1 ∧ Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀ := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.P9W at hP9
  have h := hP9 T hT
  unfold Formalism.MainNotions.DeltaInvariantLattices.p9 at h
  have hf := finrank_one W hcase
  obtain ⟨h1, _, h3⟩ := h hcase.2.1 hcase.2.2
  rw [hf, Nat.div_one] at h1
  exact ⟨h1, (h3 hf).2⟩

/- English proof (translation)
Take `⟨-, -, hγ⟩` from `p9mod_of W hcase hP9 T hT`. Take `⟨x', hx', hxx'⟩` from `hγ x hx`. Establish `hγc : W.γ T ((letE (O` using `O) c : LetA O n) • x) = (letE (O := O) c : LetA O n) • W.γ T x := by show W.γD T W.gam _ = _`. Rewrite using `[γD_smulA, γA_letE]`. Both sides reduce to the same expression.

Use `⟨hxc, hx.2, (letE (O := O) c : LetA O n) • x', smul_mem_NΔ W T (letE_mem W c) hx', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, letE_idem]`. Rewrite using `[smul_comm, ← hxx', smul_sub, ← hγc, hxc]`.
-/
theorem InI_of_N (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ) (c : ZMod n) {x : W.DD T} (hx : x ∈ W.NΔ T)
    (hxc : (letE (O := O) c : LetA O n) • x = x) : InI W T c x := by
  obtain ⟨-, -, hγ⟩ := p9mod_of W hcase hP9 T hT
  obtain ⟨x', hx', hxx'⟩ := hγ x hx
  have hγc : W.γ T ((letE (O := O) c : LetA O n) • x) = (letE (O := O) c : LetA O n) • W.γ T x := by
    show W.γD T W.gam _ = _
    rw [γD_smulA, γA_letE]
    rfl
  refine ⟨hxc, hx.2, (letE (O := O) c : LetA O n) • x', smul_mem_NΔ W T (letE_mem W c) hx', ?_, ?_⟩
  · rw [smul_smul, letE_idem]
  · rw [smul_comm, ← hxx', smul_sub, ← hγc, hxc]

/- English proof (translation)
Establish `hyl : y ∈ W.Nl T₂ c` using `⟨y, hy.1, by show ((letE (O := O) c : LetA O n) • LinearMap.id) y = y`. Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply, hyc]⟩`. Take `⟨x, hx, hxe⟩` from `hrr y hyl hy.2`. Take `⟨m, hm, hmx⟩` from `hx`. Establish `hxe' : W.map F x = Formalism.MainNotions.LiftingTheory.lp W rr • y` using `hxe`.

Establish `hx0 : x = (letE (O` using `O) c : LetA O n) • m := by rw [← hmx]; rfl`. Establish `hxN : x ∈ W.N T₁` using `by rw [hx0]; exact (W.N T₁).smul_mem _ hm`. Establish `hxc : (letE (O` using `O) c : LetA O n) • x = x := by rw [hx0, smul_smul, letE_idem]`. Establish `hFx : W.map F x = Formalism.MainNotions.LiftingTheory.lp W rr • y` using `hxe'`. Use `set avg : W.DD T₁ := ∑ δ ∈ W.DelF, W.γD T₁ δ x with havg`.

Establish `havgN : avg ∈ W.N T₁` using `Submodule.sum_mem _ fun δ _ => W.N_Γ T₁ δ x hxN`. Establish `havgΔ : ∀ δ ∈ W.DelF, W.γD T₁ δ avg = avg`. Introduce `δ hδ`. Rewrite using `[havg, map_sum]`. Use `Finset.sum_nbij' (δ * ·) (δ⁻¹ * ·) (fun g hg => delF_mul W hδ hg) (fun g hg => delF_mul W (delF_inv W hδ) hg) (fun g _ => by simp) (fun g _ => by simp) (fun g _ => ?_)` and prove the remaining obligations.

Rewrite using `[W.γD_mul]`. Establish `havgc : (letE (O` using `O) c : LetA O n) • avg = avg := by`. Rewrite using `[havg, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun δ _ => ?_` and prove the remaining obligations. Rewrite using `[← γA_letE W δ c, ← γD_smulA, hxc]`.

Establish `hFavg : W.map F avg = ((PD.p - 1 : ℕ) : O) • (Formalism.MainNotions.LiftingTheory.lp W rr • y)`. Rewrite using `[havg, map_sum]`. Establish `: ∀ δ ∈ W.DelF, W.map F (W.γD T₁ δ x) = Formalism.MainNotions.LiftingTheory.lp W rr • y`. Introduce `δ hδ`. Rewrite using `[W.map_γ, hFx, γD_smulA, hy.2 δ hδ]`.

Use `congr 1`. Simplify using `[Formalism.MainNotions.LiftingTheory.lp, map_pow, map_natCast]`. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_const, (p9mod_of W hcase hP9 T₁ hT₁).1, Nat.cast_smul_eq_nsmul]`. Use `⟨((hΔ.unit⁻¹ : Oˣ) : O) • avg, (W.NΔ T₁).smul_mem _ ⟨havgN, havgΔ⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm, havgc]`.

Rewrite using `[← algebraMap_smul (LetA O n), map_smulA, algebraMap_smul, hFavg, smul_smul, IsUnit.val_inv_mul, one_smul]`.
-/
theorem delta_lift (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (hT₁ : IsCrys PD T₁.ρ) (hΔ : IsUnit (((PD.p - 1 : ℕ) : O)))
    (c : ZMod n) (rr : ℕ) (hrr : Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    {y : W.DD T₂} (hy : y ∈ W.NΔ T₂) (hyc : (letE (O := O) c : LetA O n) • y = y) :
    ∃ x ∈ W.NΔ T₁, (letE (O := O) c : LetA O n) • x = x ∧ W.map F x = Formalism.MainNotions.LiftingTheory.lp W rr • y := by
  have hyl : y ∈ W.Nl T₂ c := ⟨y, hy.1, by
    show ((letE (O := O) c : LetA O n) • LinearMap.id) y = y
    rw [LinearMap.smul_apply, LinearMap.id_apply, hyc]⟩
  obtain ⟨x, hx, hxe⟩ := hrr y hyl hy.2
  obtain ⟨m, hm, hmx⟩ := hx
  have hxe' : W.map F x = Formalism.MainNotions.LiftingTheory.lp W rr • y := hxe
  have hx0 : x = (letE (O := O) c : LetA O n) • m := by rw [← hmx]; rfl
  have hxN : x ∈ W.N T₁ := by rw [hx0]; exact (W.N T₁).smul_mem _ hm
  have hxc : (letE (O := O) c : LetA O n) • x = x := by rw [hx0, smul_smul, letE_idem]
  have hFx : W.map F x = Formalism.MainNotions.LiftingTheory.lp W rr • y := hxe'
  set avg : W.DD T₁ := ∑ δ ∈ W.DelF, W.γD T₁ δ x with havg
  have havgN : avg ∈ W.N T₁ := Submodule.sum_mem _ fun δ _ => W.N_Γ T₁ δ x hxN
  have havgΔ : ∀ δ ∈ W.DelF, W.γD T₁ δ avg = avg := by
    intro δ hδ
    rw [havg, map_sum]
    refine Finset.sum_nbij' (δ * ·) (δ⁻¹ * ·) (fun g hg => delF_mul W hδ hg)
      (fun g hg => delF_mul W (delF_inv W hδ) hg) (fun g _ => by simp) (fun g _ => by simp)
      (fun g _ => ?_)
    rw [W.γD_mul]
  have havgc : (letE (O := O) c : LetA O n) • avg = avg := by
    rw [havg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← γA_letE W δ c, ← γD_smulA, hxc]
  have hFavg : W.map F avg = ((PD.p - 1 : ℕ) : O) • (Formalism.MainNotions.LiftingTheory.lp W rr • y) := by
    rw [havg, map_sum]
    have : ∀ δ ∈ W.DelF, W.map F (W.γD T₁ δ x) = Formalism.MainNotions.LiftingTheory.lp W rr • y := by
      intro δ hδ
      rw [W.map_γ, hFx, γD_smulA, hy.2 δ hδ]
      congr 1
      simp [Formalism.MainNotions.LiftingTheory.lp, map_pow, map_natCast]
    rw [Finset.sum_congr rfl this, Finset.sum_const, (p9mod_of W hcase hP9 T₁ hT₁).1,
      Nat.cast_smul_eq_nsmul]
  refine ⟨((hΔ.unit⁻¹ : Oˣ) : O) • avg, (W.NΔ T₁).smul_mem _ ⟨havgN, havgΔ⟩, ?_, ?_⟩
  · rw [smul_comm, havgc]
  · rw [← algebraMap_smul (LetA O n), map_smulA, algebraMap_smul, hFavg, smul_smul,
      IsUnit.val_inv_mul, one_smul]

/- English proof (translation)
Unfold `Formalism.MainNotions.LiftingTheory.lp`. Rewrite using `[← Nat.cast_pow]`. Conclude with `Nat.cast_smul_eq_nsmul _ _ _`.
-/
theorem lp_smul {T : LocLat G Qp LL O} (k : ℕ) (x : W.DD T) :
    Formalism.MainNotions.LiftingTheory.lp W k • x = (PD.p ^ k) • x := by
  unfold Formalism.MainNotions.LiftingTheory.lp
  rw [← Nat.cast_pow]
  exact Nat.cast_smul_eq_nsmul _ _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lA_eq_lp (k : ℕ) : lA W ^ k = Formalism.MainNotions.LiftingTheory.lp W k := rfl

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `h`. Use `⟨Formalism.MainNotions.LiftingTheory.lp W k • y, ?_, smul_comm _ _ _⟩` and prove the remaining obligations. Rewrite using `[lp_smul W k y]`. Unfold `Pp at hy ⊢`. Conclude with `AddSubgroup.nsmul_mem _ hy _`.
-/
theorem InFP_lp {T : LocLat G Qp LL O} {c : ZMod n} {e : ℕ} {f : LetA O n} (k : ℕ) {x : W.DD T}
    (h : InFP W T c e f x) : InFP W T c e f (Formalism.MainNotions.LiftingTheory.lp W k • x) := by
  obtain ⟨y, hy, rfl⟩ := h
  refine ⟨Formalism.MainNotions.LiftingTheory.lp W k • y, ?_, smul_comm _ _ _⟩
  rw [lp_smul W k y]
  unfold Pp at hy ⊢
  exact AddSubgroup.nsmul_mem _ hy _

/- English proof (translation)
Unfold `RepVV at h ⊢`. Take `⟨κ, κ', Hh, a, h1, h2, h3⟩` from `h`. Use `⟨κ, κ', Hh, fun k => lA W ^ r * a k, h1, fun k => ⟨W.AΔ.mul_mem (W.AΔ.pow_mem (by unfold lA; exact natCast_mem _ _) r) (h2 k).1, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← (h2 k).2]`. Unfold `lE lA`.

Simplify using `only [map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `heq : lA W ^ κ' • (lA W ^ κ • Λ • Formalism.MainNotions.LiftingTheory.lp W r • x - ∑ k, (lA W ^ r * a k) • (W.φD T ^ e) (Hh k)) = Formalism.MainNotions.LiftingTheory.lp W r • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • (W.φD T ^ e) (Hh k)))`. Rewrite using `[← lA_eq_lp W r]`. Simplify using `only [smul_sub, Finset.smul_sum, smul_smul, mul_comm, mul_left_comm, mul_assoc]`.

Rewrite using `[heq]`. Conclude with `InFP_lp W r h3`.
-/
theorem RepVV_lp {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
    {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL} (r : ℕ) {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (Formalism.MainNotions.LiftingTheory.lp W r • x) (fun k => lE W r * f k) := by
  unfold RepVV at h ⊢
  obtain ⟨κ, κ', Hh, a, h1, h2, h3⟩ := h
  refine ⟨κ, κ', Hh, fun k => lA W ^ r * a k, h1,
    fun k => ⟨W.AΔ.mul_mem (W.AΔ.pow_mem (by unfold lA; exact natCast_mem _ _) r) (h2 k).1, ?_⟩, ?_⟩
  · rw [map_mul, ← (h2 k).2]
    unfold lE lA
    simp only [map_pow, map_natCast]
    ring
  · have heq : lA W ^ κ' • (lA W ^ κ • Λ • Formalism.MainNotions.LiftingTheory.lp W r • x -
          ∑ k, (lA W ^ r * a k) • (W.φD T ^ e) (Hh k)) =
        Formalism.MainNotions.LiftingTheory.lp W r • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • (W.φD T ^ e) (Hh k))) := by
      rw [← lA_eq_lp W r]
      simp only [smul_sub, Finset.smul_sum, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    rw [heq]
    exact InFP_lp W r h3

include W in

/- English proof (translation)
Establish `hv1 : v ((PD.p : ℕ) : LL) = 1` using `W.v_l`. Establish `hu : (((PD.p - 1 : ℕ)) : LL) = ((PD.p : ℕ) : LL) + (-1)`. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_one, sub_eq_add_neg]`. Establish `hvu : v (((PD.p - 1 : ℕ)) : LL) = 0`. Rewrite using `[hu, AddValuation.map_add_of_distinct_val, hv1, AddValuation.map_neg, AddValuation.map_one]`.

Simplify using the standard rewrite rules. Rewrite using `[hv1, AddValuation.map_neg, AddValuation.map_one]`. Simplify using the standard rewrite rules. Establish `hne : (((PD.p - 1 : ℕ)) : LL) ≠ 0`. Introduce `h`.

Rewrite `hvu` using `[h, AddValuation.map_zero]`. Simplify using `at hvu`. Take `⟨y, hy⟩` from `hOv ((((PD.p - 1 : ℕ)) : LL)⁻¹) (by rw [AddValuation.map_inv, hvu]; simp)`. Establish `hmul : (((PD.p - 1 : ℕ)) : O) * y = 1` using `hinj (by rw [map_mul, hy, map_one, map_natCast, mul_inv_cancel₀ hne])`. Conclude with `⟨⟨_, y, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩`.
-/
theorem isUnit_prime_sub_one (hl : 5 ≤ PD.p) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL)) : IsUnit (((PD.p - 1 : ℕ) : O)) := by
  have hv1 : v ((PD.p : ℕ) : LL) = 1 := W.v_l
  have hu : (((PD.p - 1 : ℕ)) : LL) = ((PD.p : ℕ) : LL) + (-1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, sub_eq_add_neg]
  have hvu : v (((PD.p - 1 : ℕ)) : LL) = 0 := by
    rw [hu, AddValuation.map_add_of_distinct_val, hv1, AddValuation.map_neg, AddValuation.map_one]
    · simp
    · rw [hv1, AddValuation.map_neg, AddValuation.map_one]; simp
  have hne : (((PD.p - 1 : ℕ)) : LL) ≠ 0 := by
    intro h; rw [h, AddValuation.map_zero] at hvu; simp at hvu
  obtain ⟨y, hy⟩ := hOv ((((PD.p - 1 : ℕ)) : LL)⁻¹) (by rw [AddValuation.map_inv, hvu]; simp)
  have hmul : (((PD.p - 1 : ℕ)) : O) * y = 1 :=
    hinj (by rw [map_mul, hy, map_one, map_natCast, mul_inv_cancel₀ hne])
  exact ⟨⟨_, y, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

/- English proof (translation)
Establish `hj : A.j ≤ A.len c` using `hA.2.2.2.1 c hc`. Establish `hFil : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs → dvO W T₂ (A.len c) b (Pi.single k₀ (1 : O)) ∈ FilS W T₂ c s bs`. Introduce `s hs bs hbs`. Establish `h` using `hk₀ s hs bs hbs`. Unfold `dvO`.

Use `h using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`. Break down `eq_or_ne m k₀ with rfl | hm` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hm]`.

Establish `hg` using `hNN hcase hl A hA c hc T₂ hW₂ d b sol hb (Pi.single k₀ (1 : O)) hFil f hfnn`. Establish `hAr` using `hArc hcase hl A hA c hc (A.len c) hj le_rfl`. Simplify using `only at hAr`. Rewrite `hAr` using `[sub_add_cancel]`. Take `⟨-, hAT⟩` from `hAr`.

Take `⟨-, hNP, -, hfr⟩` from `hAT T₂ hW₂`. Take `⟨-, -, -, -, hNL, -, -⟩` from `hfr d b sol hb`. Take `⟨x₂, ⟨y₂, hy₂, hyc, rfl⟩, hR⟩` from `hNL _ hg`. Take `⟨x₁, hx₁, hx₁c, hFx⟩` from `delta_lift W hcase hP9 F hW₁.1 hΔ c rr hrr hy₂ hyc`. Use `⟨x₁, 0, InI_of_N W hcase hP9 hW₁.1 c hx₁ hx₁c, ⟨1, (Ps W).one_mem, x₁, hx₁, hx₁c, rfl⟩, ?_, ⟨0, (W.NΔ T₂).zero_mem, smul_zero _, (smul_zero _).symm⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hFx]`. Apply `hNP` to reduce the goal to its premises. Use `⟨Formalism.MainNotions.LiftingTheory.lp W rr • y₂, ?_, by rw [smul_comm, hyc], (one_smul _ _).symm⟩` and prove the remaining obligations. Rewrite using `[lp_smul]`. Conclude with `(W.NΔ T₂).toAddSubmonoid.nsmul_mem hy₂ _`.

Rewrite using `[hFx, sub_zero]`. Establish `h2` using `RepVV_lp W rr hR`. Simplify using `only [one_smul] at h2`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Break down `eq_or_ne k k₀ with rfl | hk` into its components or cases. Simplify using `[lE, pow_add, mul_comm, mul_left_comm]`. Simplify using `[Pi.single_eq_of_ne hk, hk]`.
-/
theorem ntype_core (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (A : ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (hArc : ArcCore W) (hNN : UnivNNCore W) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂)
    (hΔ : IsUnit (((PD.p - 1 : ℕ) : O))) (rr : ℕ) (hrr : Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLppT W A T₂ c b k₀)
    (f : W.EE) (hfnn : InFr W c (nnNum W A c) (nnDen W A c) f) :
    LiftsAtT W A F c b sol k₀ f (rr + A.σ PD.p) := by
  have hj : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hFil : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T₂ (A.len c) b (Pi.single k₀ (1 : O)) ∈ FilS W T₂ c s bs := by
    intro s hs bs hbs
    have h := hk₀ s hs bs hbs
    unfold dvO
    convert h using 2
    funext m
    rcases eq_or_ne m k₀ with rfl | hm
    · simp
    · simp [Pi.single_eq_of_ne hm]
  have hg := hNN hcase hl A hA c hc T₂ hW₂ d b sol hb (Pi.single k₀ (1 : O)) hFil f hfnn
  have hAr := hArc hcase hl A hA c hc (A.len c) hj le_rfl
  dsimp only at hAr
  rw [sub_add_cancel] at hAr
  obtain ⟨-, hAT⟩ := hAr
  obtain ⟨-, hNP, -, hfr⟩ := hAT T₂ hW₂
  obtain ⟨-, -, -, -, hNL, -, -⟩ := hfr d b sol hb
  obtain ⟨x₂, ⟨y₂, hy₂, hyc, rfl⟩, hR⟩ := hNL _ hg
  obtain ⟨x₁, hx₁, hx₁c, hFx⟩ := delta_lift W hcase hP9 F hW₁.1 hΔ c rr hrr hy₂ hyc
  refine ⟨x₁, 0, InI_of_N W hcase hP9 hW₁.1 c hx₁ hx₁c,
    ⟨1, (Ps W).one_mem, x₁, hx₁, hx₁c, rfl⟩, ?_,
    ⟨0, (W.NΔ T₂).zero_mem, smul_zero _, (smul_zero _).symm⟩, ?_⟩
  · rw [hFx]
    apply hNP
    refine ⟨Formalism.MainNotions.LiftingTheory.lp W rr • y₂, ?_, by rw [smul_comm, hyc], (one_smul _ _).symm⟩
    rw [lp_smul]
    exact (W.NΔ T₂).toAddSubmonoid.nsmul_mem hy₂ _
  · rw [hFx, sub_zero]
    have h2 := RepVV_lp W rr hR
    simp only [one_smul] at h2
    convert h2 using 1
    funext k
    rcases eq_or_ne k k₀ with rfl | hk
    · simp [lE, pow_add, mul_comm, mul_left_comm]
    · simp [Pi.single_eq_of_ne hk, hk]

section Bez

/- English proof (translation)
Establish `h` using `hP9 T hT`. Unfold `Formalism.MainNotions.DeltaInvariantLattices.p9 at h`. Establish `hf` using `finrank_one W hcase`. Establish `h3` using `((h hcase.2.1 hcase.2.2).2.2 hf).1`. Unfold `Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations at h3`.

Unfold `GS.RD`. Take `⟨_, h2, h3', _, _, h6, h7, _⟩` from `h3`. Establish `hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = W.π₀ + lA W`. Unfold `Formalism.MainNotions.DeltaInvariantLattices.Eat lA`. Use function extensionality and compare the values at `i`.

Simplify using `[Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]`. Use `⟨h3', ?_, ?_, fun a ha => (h2 a ha).exists⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `h6`. Use `⟨w, ?_⟩` and prove the remaining obligations. Unfold `qA`.

Rewrite using `[hw, hE]`. Take `⟨w, hw⟩` from `h7`. Use `⟨w, ?_⟩` and prove the remaining obligations. Unfold `qA`. Rewrite using `[hw, hE]`.
-/
theorem ringData_of_crystalline (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) : GS.RD W := by
  have h := hP9 T hT
  unfold Formalism.MainNotions.DeltaInvariantLattices.p9 at h
  have hf := finrank_one W hcase
  have h3 := ((h hcase.2.1 hcase.2.2).2.2 hf).1
  unfold Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations at h3
  unfold GS.RD
  obtain ⟨_, h2, h3', _, _, h6, h7, _⟩ := h3
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = W.π₀ + lA W := by
    unfold Formalism.MainNotions.DeltaInvariantLattices.Eat lA
    funext i
    simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  refine ⟨h3', ?_, ?_, fun a ha => (h2 a ha).exists⟩
  · obtain ⟨w, hw⟩ := h6; refine ⟨w, ?_⟩; unfold qA; rw [hw, hE]
  · obtain ⟨w, hw⟩ := h7; refine ⟨w, ?_⟩; unfold qA; rw [hw, hE]

variable {W}

/- English proof (translation)
Unfold `lA`. Conclude with `natCast_mem _ _`.
-/
theorem lA_mem' : lA W ∈ W.AΔ := by
  unfold lA
  exact natCast_mem _ _

/- English proof (translation)
Take `⟨-, ⟨w, hw⟩, -⟩` from `id hR`. Use `⟨w, GS.quot_mem W (c := W.π₀ * qA W ^ (PD.p - 1)) (W.AΔ.mul_mem (GS.π₀_mem W) (W.AΔ.pow_mem (GS.qA_mem W) _)) ?_ ?_, by rw [hw]⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Conclude with `(GS.isUnit_π₀ hR).mul ((GS.isUnit_qA hR).pow _)`. Establish `e : W.π₀ * qA W ^ (PD.p - 1) * (w : LetA O n) = W.φA W.π₀` using `by rw [hw]; ring`.

Rewrite using `[e]`. Use `GS.φpow_mem W 1 (GS.π₀_mem W)` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem w_mem (hR : GS.RD W) : ∃ w ∈ W.AΔ, W.φA W.π₀ = w * W.π₀ * qA W ^ (PD.p - 1) := by
  obtain ⟨-, ⟨w, hw⟩, -⟩ := id hR
  refine ⟨w, GS.quot_mem W (c := W.π₀ * qA W ^ (PD.p - 1))
    (W.AΔ.mul_mem (GS.π₀_mem W) (W.AΔ.pow_mem (GS.qA_mem W) _)) ?_ ?_, by rw [hw]⟩
  · rw [map_mul, map_pow]
    exact (GS.isUnit_π₀ hR).mul ((GS.isUnit_qA hR).pow _)
  · have e : W.π₀ * qA W ^ (PD.p - 1) * (w : LetA O n) = W.φA W.π₀ := by rw [hw]; ring
    rw [e]
    have := GS.φpow_mem W 1 (GS.π₀_mem W)
    rwa [pow_one] at this

/- English proof (translation)
Take `⟨w, hw, hφ⟩` from `w_mem hR`. Introduce `s`. Proceed by induction on `s with`. Consider the case `zero => intro k hk`. Use linear arithmetic over natural numbers and integers.

Consider the case `succ s ih`. Introduce `k hk`. Establish `e : (W.φA ^ (s + 1)) W.π₀ = (W.φA ^ s) w * (W.φA ^ s) W.π₀ * ps W s ^ (PD.p - 1)`. Rewrite using `[pow_succ, AlgHom.mul_apply, hφ, map_mul, map_mul, map_pow]`. Both sides reduce to the same expression.

Establish `hwm : (W.φA ^ s) w ∈ W.AΔ` using `GS.φpow_mem W s hw`. Establish `hπm : (W.φA ^ s) W.π₀ ∈ W.AΔ` using `GS.φpow_mem W s (GS.π₀_mem W)`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl` into its components or cases. Take `⟨h, hh, he⟩` from `ih k hk`. Conclude with `⟨(W.φA ^ s) w * h * ps W s ^ (PD.p - 1), W.AΔ.mul_mem (W.AΔ.mul_mem hwm hh) (W.AΔ.pow_mem (GS.ps_mem W s) _), by rw [e, he]; ring⟩`.

Establish `hp2 : PD.p - 1 = (PD.p - 2) + 1` using `by have := PD.hp.two_le; omega`. Conclude with `⟨(W.φA ^ k) w * (W.φA ^ k) W.π₀ * ps W k ^ (PD.p - 2), W.AΔ.mul_mem (W.AΔ.mul_mem hwm hπm) (W.AΔ.pow_mem (GS.ps_mem W k) _), by rw [e, hp2, pow_succ]; ring⟩`.
-/
theorem φpow_π₀_dvd (hR : GS.RD W) : ∀ s : ℕ, ∀ k < s, ∃ h ∈ W.AΔ, (W.φA ^ s) W.π₀ = ps W k * h := by
  obtain ⟨w, hw, hφ⟩ := w_mem hR
  intro s
  induction s with
  | zero => intro k hk; omega
  | succ s ih =>
    intro k hk
    have e : (W.φA ^ (s + 1)) W.π₀ = (W.φA ^ s) w * (W.φA ^ s) W.π₀ * ps W s ^ (PD.p - 1) := by
      rw [pow_succ, AlgHom.mul_apply, hφ, map_mul, map_mul, map_pow]
      rfl
    have hwm : (W.φA ^ s) w ∈ W.AΔ := GS.φpow_mem W s hw
    have hπm : (W.φA ^ s) W.π₀ ∈ W.AΔ := GS.φpow_mem W s (GS.π₀_mem W)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · obtain ⟨h, hh, he⟩ := ih k hk
      exact ⟨(W.φA ^ s) w * h * ps W s ^ (PD.p - 1),
        W.AΔ.mul_mem (W.AΔ.mul_mem hwm hh) (W.AΔ.pow_mem (GS.ps_mem W s) _), by rw [e, he]; ring⟩
    · have hp2 : PD.p - 1 = (PD.p - 2) + 1 := by have := PD.hp.two_le; omega
      exact ⟨(W.φA ^ k) w * (W.φA ^ k) W.π₀ * ps W k ^ (PD.p - 2),
        W.AΔ.mul_mem (W.AΔ.mul_mem hwm hπm) (W.AΔ.pow_mem (GS.ps_mem W k) _),
        by rw [e, hp2, pow_succ]; ring⟩

/- English proof (translation)
Take `⟨h, hh, he⟩` from `φpow_π₀_dvd hR s k hk`. Use `⟨h, hh, ?_⟩` and prove the remaining obligations. Establish `e : ps W s = (W.φA ^ s) W.π₀ + lA W`. Unfold `ps qA`. Rewrite using `[map_add]`.

Use `congr 1`. Unfold `lA`. Conclude with `map_natCast _ _`. Rewrite using `[e, he]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ps_eq (hR : GS.RD W) {s k : ℕ} (hk : k < s) : ∃ h ∈ W.AΔ, ps W s = lA W + ps W k * h := by
  obtain ⟨h, hh, he⟩ := φpow_π₀_dvd hR s k hk
  refine ⟨h, hh, ?_⟩
  have e : ps W s = (W.φA ^ s) W.π₀ + lA W := by
    unfold ps qA
    rw [map_add]
    congr 1
    unfold lA
    exact map_natCast _ _
  rw [e, he]
  ring

/- English proof (translation)
Set `x : W.AΔ` to `⟨X, hX⟩`. Set `y : W.AΔ` to `⟨Y * g, W.AΔ.mul_mem hY hg⟩`. Set `yy : W.AΔ` to `⟨Y, hY⟩`. Set `I : Ideal W.AΔ` to `Ideal.span {x ^ a, yy ^ b}`. Establish `hxa : x ^ a ∈ I` using `Ideal.subset_span (Set.mem_insert _ _)`.

Establish `hyyb : yy ^ b ∈ I` using `Ideal.subset_span (Set.mem_insert_of_mem _ rfl)`. Establish `hyb : y ^ b ∈ I`. Establish `hyg : y = (⟨g, hg⟩ : W.AΔ) * yy`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [y, yy, Subalgebra.coe_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hyg, mul_pow]`. Conclude with `I.mul_mem_left _ hyyb`. Establish `hmem : (x + y) ^ (a * b) ∈ I`. Break down `Nat.eq_zero_or_pos a with ha | ha` into its components or cases.

Rewrite `hxa` using `[ha, pow_zero]`. Rewrite using `[Ideal.eq_top_of_isUnit_mem _ hxa isUnit_one]`. Conclude with `Submodule.mem_top`. Break down `Nat.eq_zero_or_pos b with hb | hb` into its components or cases. Rewrite `hyyb` using `[hb, pow_zero]`.

Rewrite using `[Ideal.eq_top_of_isUnit_mem _ hyyb isUnit_one]`. Conclude with `Submodule.mem_top`. Establish `h1 : 1 ≤ a` using `ha`. Establish `h2 : 1 ≤ b` using `hb`. Conclude with `Ideal.add_pow_mem_of_pow_mem_of_le (I := I) hxa hyb (by nlinarith)`.

Rewrite `hmem` using `[Ideal.mem_span_pair]`. Take `⟨α, β, h⟩` from `hmem`. Use `⟨α, α.2, β, β.2, ?_⟩` and prove the remaining obligations. Establish `h'` using `congrArg Subtype.val h`. Simplify using `only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow, x, y, yy] at h'`.

Rewrite using `[he, h']`.
-/
theorem bez_pow {X Y g : LetA O n} (hX : X ∈ W.AΔ) (hY : Y ∈ W.AΔ) (hg : g ∈ W.AΔ)
    (he : lA W = X + Y * g) (a b : ℕ) :
    ∃ α ∈ W.AΔ, ∃ β ∈ W.AΔ, α * X ^ a + β * Y ^ b = lA W ^ (a * b) := by
  let x : W.AΔ := ⟨X, hX⟩
  let y : W.AΔ := ⟨Y * g, W.AΔ.mul_mem hY hg⟩
  let yy : W.AΔ := ⟨Y, hY⟩
  let I : Ideal W.AΔ := Ideal.span {x ^ a, yy ^ b}
  have hxa : x ^ a ∈ I := Ideal.subset_span (Set.mem_insert _ _)
  have hyyb : yy ^ b ∈ I := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hyb : y ^ b ∈ I := by
    have hyg : y = (⟨g, hg⟩ : W.AΔ) * yy := by
      apply Subtype.ext; simp only [y, yy, Subalgebra.coe_mul]; ring
    rw [hyg, mul_pow]
    exact I.mul_mem_left _ hyyb
  have hmem : (x + y) ^ (a * b) ∈ I := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, pow_zero] at hxa
      rw [Ideal.eq_top_of_isUnit_mem _ hxa isUnit_one]; exact Submodule.mem_top
    rcases Nat.eq_zero_or_pos b with hb | hb
    · rw [hb, pow_zero] at hyyb
      rw [Ideal.eq_top_of_isUnit_mem _ hyyb isUnit_one]; exact Submodule.mem_top
    have h1 : 1 ≤ a := ha
    have h2 : 1 ≤ b := hb
    exact Ideal.add_pow_mem_of_pow_mem_of_le (I := I) hxa hyb (by nlinarith)
  rw [Ideal.mem_span_pair] at hmem
  obtain ⟨α, β, h⟩ := hmem
  refine ⟨α, α.2, β, β.2, ?_⟩
  have h' := congrArg Subtype.val h
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow, x, y, yy] at h'
  rw [he, h']

/- English proof (translation)
Break down `lt_or_gt_of_ne hst with h | h` into its components or cases. Take `⟨g, hg, he⟩` from `ps_eq hR h`. Establish `he' : lA W = ps W t + ps W s * (-g)` using `by rw [he]; ring`. Take `⟨α, hα, β, hβ, e⟩` from `bez_pow (GS.ps_mem W t) (GS.ps_mem W s) (neg_mem hg) he' b a`. Conclude with `⟨b * a, β, hβ, α, hα, by rw [← e]; ring⟩`.

Take `⟨g, hg, he⟩` from `ps_eq hR h`. Establish `he' : lA W = ps W s + ps W t * (-g)` using `by rw [he]; ring`. Take `⟨α, hα, β, hβ, e⟩` from `bez_pow (GS.ps_mem W s) (GS.ps_mem W t) (neg_mem hg) he' a b`. Conclude with `⟨a * b, α, hα, β, hβ, e⟩`.
-/
theorem bez_ps (hR : GS.RD W) {s t : ℕ} (hst : s ≠ t) (a b : ℕ) :
    ∃ K, ∃ α ∈ W.AΔ, ∃ β ∈ W.AΔ, α * ps W s ^ a + β * ps W t ^ b = lA W ^ K := by
  rcases lt_or_gt_of_ne hst with h | h
  · obtain ⟨g, hg, he⟩ := ps_eq hR h
    have he' : lA W = ps W t + ps W s * (-g) := by rw [he]; ring
    obtain ⟨α, hα, β, hβ, e⟩ := bez_pow (GS.ps_mem W t) (GS.ps_mem W s) (neg_mem hg) he' b a
    exact ⟨b * a, β, hβ, α, hα, by rw [← e]; ring⟩
  · obtain ⟨g, hg, he⟩ := ps_eq hR h
    have he' : lA W = ps W s + ps W t * (-g) := by rw [he]; ring
    obtain ⟨α, hα, β, hβ, e⟩ := bez_pow (GS.ps_mem W s) (GS.ps_mem W t) (neg_mem hg) he' a b
    exact ⟨a * b, α, hα, β, hβ, e⟩

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => intro _; exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩`. Consider the case `succ N ih`. Introduce `hN`.

Take `⟨K₁, α₁, hα₁, β₁, hβ₁, e₁⟩` from `ih (by omega)`. Take `⟨K₂, α₂, hα₂, β₂, hβ₂, e₂⟩` from `bez_ps hR (show N ≠ t by omega) (m N) b`. Establish `hP : (∏ s ∈ Finset.range N, ps W s ^ m s) ∈ W.AΔ` using `Subalgebra.prod_mem _ fun s _ => W.AΔ.pow_mem (GS.ps_mem W s) _`. Establish `hQ : ps W N ^ m N ∈ W.AΔ` using `W.AΔ.pow_mem (GS.ps_mem W N) _`. Establish `hC : ps W t ^ b ∈ W.AΔ` using `W.AΔ.pow_mem (GS.ps_mem W t) _`.

Use `⟨K₁ + K₂, α₁ * α₂, W.AΔ.mul_mem hα₁ hα₂, β₁ * α₂ * ps W N ^ m N + α₁ * (∏ s ∈ Finset.range N, ps W s ^ m s) * β₂ + β₁ * β₂ * ps W t ^ b, W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hβ₁ hα₂) hQ) (W.AΔ.mul_mem (W.AΔ.mul_mem hα₁ hP) hβ₂)) (W.AΔ.mul_mem (W.AΔ.mul_mem hβ₁ h …` and prove the remaining obligations. Rewrite using `[Finset.prod_range_succ, pow_add]`. Take the linear combination `(α₂ * ps W N ^ m N + β₂ * ps W t ^ b) * e₁ + lA W ^ K₁ * e₂`.
-/
theorem bez_prod (hR : GS.RD W) (m : ℕ → ℕ) (t b : ℕ) : ∀ N ≤ t,
    ∃ K, ∃ α ∈ W.AΔ, ∃ β ∈ W.AΔ,
      α * (∏ s ∈ Finset.range N, ps W s ^ m s) + β * ps W t ^ b = lA W ^ K := by
  intro N
  induction N with
  | zero => intro _; exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | succ N ih =>
    intro hN
    obtain ⟨K₁, α₁, hα₁, β₁, hβ₁, e₁⟩ := ih (by omega)
    obtain ⟨K₂, α₂, hα₂, β₂, hβ₂, e₂⟩ := bez_ps hR (show N ≠ t by omega) (m N) b
    have hP : (∏ s ∈ Finset.range N, ps W s ^ m s) ∈ W.AΔ :=
      Subalgebra.prod_mem _ fun s _ => W.AΔ.pow_mem (GS.ps_mem W s) _
    have hQ : ps W N ^ m N ∈ W.AΔ := W.AΔ.pow_mem (GS.ps_mem W N) _
    have hC : ps W t ^ b ∈ W.AΔ := W.AΔ.pow_mem (GS.ps_mem W t) _
    refine ⟨K₁ + K₂, α₁ * α₂, W.AΔ.mul_mem hα₁ hα₂,
      β₁ * α₂ * ps W N ^ m N + α₁ * (∏ s ∈ Finset.range N, ps W s ^ m s) * β₂ + β₁ * β₂ * ps W t ^ b,
      W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hβ₁ hα₂) hQ)
        (W.AΔ.mul_mem (W.AΔ.mul_mem hα₁ hP) hβ₂)) (W.AΔ.mul_mem (W.AΔ.mul_mem hβ₁ hβ₂) hC), ?_⟩
    rw [Finset.prod_range_succ, pow_add]
    linear_combination (α₂ * ps W N ^ m N + β₂ * ps W t ^ b) * e₁ + lA W ^ K₁ * e₂

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => intro _; exact ⟨U, hU, by simp⟩`. Consider the case `succ N ih`. Introduce `hdiv`.

Take `⟨u, hu, hUu⟩` from `ih fun s hs => hdiv s (by omega)`. Take `⟨v, hv, hUv⟩` from `hdiv N (by omega)`. Take `⟨K, α, hα, β, hβ, e⟩` from `bez_prod hR m N (m N) N le_rfl`. Establish `hC : ps W N ^ m N ∈ PiPs W` using `by show ps W N ^ m N ∈ Submonoid.closure (insert W.π₀ (Set.range (ps W)))`. Conclude with `Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self N))) _`.

Take `⟨y, hy, hyu⟩` from `saturation_fraction_ring W hcase hP9 hinj (ps W N ^ m N) 1 1 hC (PiPs W).one_mem (PiPs W).one_mem u (by rw [one_mul]; exact hu) ⟨K, α * v + β * u, W.AΔ.add_mem (W.AΔ.mul_mem hα hv) (W.AΔ.mul_mem hβ hu), by`. Rewrite using `[one_mul, ← e]`. Take the linear combination `α * hUv - α * hUu⟩`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite `*` using `[Finset.prod_range_succ, hUu, one_mul]`.

Rewrite using `[hyu]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem div_prod [FiniteDimensional Qp LL] [IsDomain O] [IsDiscreteValuationRing O] (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hinj : Function.Injective (algebraMap O LL)) (hR : GS.RD W)
    (m : ℕ → ℕ) {U : LetA O n} (hU : U ∈ W.AΔ) :
    ∀ N, (∀ s < N, ∃ v ∈ W.AΔ, U = ps W s ^ m s * v) →
      ∃ u ∈ W.AΔ, U = (∏ s ∈ Finset.range N, ps W s ^ m s) * u := by
  intro N
  induction N with
  | zero => intro _; exact ⟨U, hU, by simp⟩
  | succ N ih =>
    intro hdiv
    obtain ⟨u, hu, hUu⟩ := ih fun s hs => hdiv s (by omega)
    obtain ⟨v, hv, hUv⟩ := hdiv N (by omega)
    obtain ⟨K, α, hα, β, hβ, e⟩ := bez_prod hR m N (m N) N le_rfl
    have hC : ps W N ^ m N ∈ PiPs W := by
      show ps W N ^ m N ∈ Submonoid.closure (insert W.π₀ (Set.range (ps W)))
      exact Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self N))) _
    obtain ⟨y, hy, hyu⟩ := saturation_fraction_ring W hcase hP9 hinj (ps W N ^ m N) 1 1 hC (PiPs W).one_mem
      (PiPs W).one_mem u (by rw [one_mul]; exact hu)
      ⟨K, α * v + β * u, W.AΔ.add_mem (W.AΔ.mul_mem hα hv) (W.AΔ.mul_mem hβ hu), by
        rw [one_mul, ← e]
        linear_combination α * hUv - α * hUu⟩
    refine ⟨y, hy, ?_⟩
    rw [Finset.prod_range_succ, hUu, one_mul] at *
    rw [hyu]
    ring

end Bez

/- English proof (translation)
Take `⟨u₀, hu₀, e₀⟩` from `hf`. Establish `hUm : (letE (O` using `O) c : LetA O n) * u₀ ∈ W.AΔ := W.AΔ.mul_mem (letE_mem W c) hu₀`. Establish `key : ∃ u ∈ W.AΔ, (letE (O` using `O) c : LetA O n) * u₀ = nnNum W A c * u := by`. Unfold `nnNum prodTy`. Use `div_prod hcase hP9 hinj hR _ hUm (A.len c) fun s hs => ?_` and prove the remaining obligations.

Break down `hty : A.ty (c - (s : ZMod n)) with _ | bs | bs` into its components or cases. Establish `h` using `hthick s hs`. Rewrite `h` using `[hty]`. Conclude with `absurd h (by decide)`. Conclude with `⟨_, hUm, by simp⟩`.

Take `⟨u₁, hu₁, e₁⟩` from `hdown s hs bs hty`. Use `⟨(letE (O := O) c : LetA O n) * u₁, W.AΔ.mul_mem (letE_mem W c) hu₁, ?_⟩` and prove the remaining obligations. Establish `e` using `W.EE_inj (e₀.symm.trans e₁)`. Simplify using `only`. Take the linear combination `e`.

Take `⟨u, hu, hUu⟩` from `key`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[e₀]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, letE_idem, mul_one]`. Use `_ = (letE (O := O) c : LetA O n) * nnNum W A c * u := by rw [hUu, mul_assoc]`.
-/
theorem nn_of [FiniteDimensional Qp LL] [IsDomain O] [IsDiscreteValuationRing O]
    (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hinj : Function.Injective (algebraMap O LL))
    (hR : GS.RD W) (A : ArcP n) (c : ZMod n)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (f : W.EE)
    (hf : InFr W c 1 (nnDen W A c) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c) f) :
    InFr W c (nnNum W A c) (nnDen W A c) f := by
  obtain ⟨u₀, hu₀, e₀⟩ := hf
  have hUm : (letE (O := O) c : LetA O n) * u₀ ∈ W.AΔ := W.AΔ.mul_mem (letE_mem W c) hu₀
  have key : ∃ u ∈ W.AΔ, (letE (O := O) c : LetA O n) * u₀ = nnNum W A c * u := by
    unfold nnNum prodTy
    refine div_prod hcase hP9 hinj hR _ hUm (A.len c) fun s hs => ?_
    rcases hty : A.ty (c - (s : ZMod n)) with _ | bs | bs
    · have h := hthick s hs
      rw [hty] at h
      exact absurd h (by decide)
    · exact ⟨_, hUm, by simp⟩
    · obtain ⟨u₁, hu₁, e₁⟩ := hdown s hs bs hty
      refine ⟨(letE (O := O) c : LetA O n) * u₁, W.AΔ.mul_mem (letE_mem W c) hu₁, ?_⟩
      have e := W.EE_inj (e₀.symm.trans e₁)
      simp only
      linear_combination e
  obtain ⟨u, hu, hUu⟩ := key
  refine ⟨u, hu, ?_⟩
  rw [e₀]
  congr 1
  calc (letE (O := O) c : LetA O n) * 1 * u₀
      = (letE (O := O) c : LetA O n) * ((letE (O := O) c : LetA O n) * u₀) := by
        rw [← mul_assoc, letE_idem, mul_one]
    _ = (letE (O := O) c : LetA O n) * nnNum W A c * u := by rw [hUu, mul_assoc]

/- English proof (translation)
Unfold `LiftsAtT at h ⊢`. Take `⟨w₁, z, hw, hΛ, hP, hz, κ, κ', H, a, hH, ha, hR⟩` from `h`. Establish `hLam : abelian₂ W A c (A.len c) ∈ W.AΔ` using `Subalgebra.prod_mem _ fun s _ => W.AΔ.pow_mem (GS.ps_mem W s) _`. Establish `hx : algebraMap O W.EE x = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x)` using `IsScalarTower.algebraMap_apply O (LetA O n) W.EE x`. Establish `hlE : lE W e = algebraMap (LetA O n) W.EE (lA W ^ e)`.

Unfold `lE lA`. Rewrite using `[map_pow, map_natCast]`. Set `a' : Fin d → LetA O n` to `fun k => if k = k₀ then abelian₂ W A c (A.len c) * lA W ^ e * algebraMap O (LetA O n) x else 0`. Establish `ha' : ∀ k, a k = letE c * a' k`. Introduce `k`.

Apply `W.EE_inj` to reduce the goal to its premises. Rewrite using `[← (ha k).2]`. Simplify using `only [a']`. Use `split_ifs`. Rewrite using `[hx, hlE]`.

Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Use `⟨w₁, z, hw, hΛ, hP, hz, κ, κ', H, a', hH, fun k => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [a'] split_ifs`.

Conclude with `W.AΔ.mul_mem (W.AΔ.mul_mem hLam (W.AΔ.pow_mem lA_mem' _)) (Subalgebra.algebraMap_mem _ _)`. Conclude with `W.AΔ.zero_mem`. Simplify using `only [a'] split_ifs`. Rewrite using `[hx, hlE]`. Simplify using `only [map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `hs : ∑ k, a' k • ((W.φD T₂) ^ (A.len c)) (H k) = ∑ k, a k • ((W.φD T₂) ^ (A.len c)) (H k)`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[ha' k, mul_smul, smul_comm]`.

Use `congr 1`. Use `TypesD.φDpow_letter W (TypesD.horTr_letter W hb (hH k)) (A.len c)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `this.symm`. Rewrite using `[hs]`.

Conclude with `hR`.
-/
theorem letter_const [FiniteDimensional Qp LL] (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (c : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (x : O) {e : ℕ}
    (h : LiftsAtT W A F c b sol k₀
      (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x) e) :
    LiftsAtT W A F c b sol k₀ (algebraMap O W.EE x) e := by
  unfold LiftsAtT at h ⊢
  obtain ⟨w₁, z, hw, hΛ, hP, hz, κ, κ', H, a, hH, ha, hR⟩ := h
  have hLam : abelian₂ W A c (A.len c) ∈ W.AΔ :=
    Subalgebra.prod_mem _ fun s _ => W.AΔ.pow_mem (GS.ps_mem W s) _
  have hx : algebraMap O W.EE x = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x) :=
    IsScalarTower.algebraMap_apply O (LetA O n) W.EE x
  have hlE : lE W e = algebraMap (LetA O n) W.EE (lA W ^ e) := by
    unfold lE lA
    rw [map_pow, map_natCast]
  let a' : Fin d → LetA O n := fun k =>
    if k = k₀ then abelian₂ W A c (A.len c) * lA W ^ e * algebraMap O (LetA O n) x else 0
  have ha' : ∀ k, a k = letE c * a' k := by
    intro k
    apply W.EE_inj
    rw [← (ha k).2]
    simp only [a']
    split_ifs
    · rw [hx, hlE]
      simp only [map_mul]
      ring
    · simp
  refine ⟨w₁, z, hw, hΛ, hP, hz, κ, κ', H, a', hH, fun k => ⟨?_, ?_⟩, ?_⟩
  · simp only [a']
    split_ifs
    · exact W.AΔ.mul_mem (W.AΔ.mul_mem hLam (W.AΔ.pow_mem lA_mem' _)) (Subalgebra.algebraMap_mem _ _)
    · exact W.AΔ.zero_mem
  · simp only [a']
    split_ifs
    · rw [hx, hlE]
      simp only [map_mul]
      ring
    · simp
  · have hs : ∑ k, a' k • ((W.φD T₂) ^ (A.len c)) (H k) =
        ∑ k, a k • ((W.φD T₂) ^ (A.len c)) (H k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ha' k, mul_smul, smul_comm]
      congr 1
      have := TypesD.φDpow_letter W (TypesD.horTr_letter W hb (hH k)) (A.len c)
      rw [sub_add_cancel] at this
      exact this.symm
    rw [hs]
    exact hR

end Formalism.MainNotions.N.FrobeniusPowerSeries.NTB
