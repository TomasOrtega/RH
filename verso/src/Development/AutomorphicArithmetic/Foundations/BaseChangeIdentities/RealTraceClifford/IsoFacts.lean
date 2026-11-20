import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Simplify using `[rt, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]`.
-/
private theorem dot_rt {n : ℕ} (x : Wt n) (a b : Fin n) : ∑ c, x c * rt a b c = x a - x b := by
  simp [rt, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

/- English proof (translation)
Simplify using `[mul_add, Finset.sum_add_distrib]`.
-/
private theorem dot_add {n : ℕ} (x u v : Wt n) :
    ∑ c, x c * (u + v) c = ∑ c, x c * u c + ∑ c, x c * v c := by
  simp [mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Introduce `c`. Establish `h` using `LinearMap.congr_fun (hg c c a b) y`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Rewrite `h` using `[hy c, map_smul, sub_eq_iff_eq_add]`. Rewrite using `[h]`.

Apply the tactic sequence `by_cases hca : c = a <;> by_cases hcb : c = b`. Substitute `hca` using the available equality. Substitute `hcb` using the available equality. Simplify using `[rt]`. Substitute `hca` using the available equality.

Simplify using `[rt, Pi.single_apply, hcb, Ne.symm hcb, add_smul]`. Normalize the expressions using the abelian group laws. Substitute `hcb` using the available equality. Simplify using `[rt, Pi.single_apply, hca, Ne.symm hca, add_smul, sub_smul]`. Normalize the expressions using the abelian group laws.

Simplify using `[rt, Pi.single_apply, hca, hcb, Ne.symm hcb]`.
-/
private theorem wt_shift {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hg : GlRel F) {μ : Wt n} {y : V}
    (hy : IsWeight F μ y) (a b : Fin n) : IsWeight F (μ + rt a b) (F a b y) := by
  intro c
  have h := LinearMap.congr_fun (hg c c a b) y
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hy c, map_smul, sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb
    simp [rt]
  · subst hca
    simp [rt, Pi.single_apply, hcb, Ne.symm hcb, add_smul]
    abel
  · subst hcb
    simp [rt, Pi.single_apply, hca, Ne.symm hca, add_smul, sub_smul]
    abel
  · simp [rt, Pi.single_apply, hca, hcb, Ne.symm hcb]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simpa [Formalism.REAL.ew] using hx`. Consider the case `cons p w ih`. Establish `h` using `wt_shift hg ih p.1 p.2`. Rewrite using `[Formalism.REAL.ew.eq_2]`.

Simplify using `only [List.map_cons, List.sum_cons, Module.End.mul_apply]`. Rewrite using `[show ∀ u v : Wt n, μ + (u + v) = (μ + v) + u from fun u v => by abel]` and apply the resulting hypothesis.
-/
private theorem wt_word {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hg : GlRel F) {μ : Wt n} {x : V}
    (hx : IsWeight F μ x) (w : List (Fin n × Fin n)) :
    IsWeight F (μ + (w.map fun p => rt p.1 p.2).sum) (Formalism.REAL.ew F w x) := by
  induction w with
  | nil => simpa [Formalism.REAL.ew] using hx
  | cons p w ih =>
    have h := wt_shift hg ih p.1 p.2
    rw [Formalism.REAL.ew.eq_2]
    simp only [List.map_cons, List.sum_cons, Module.End.mul_apply]
    rwa [show ∀ u v : Wt n, μ + (u + v) = (μ + v) + u from fun u v => by abel]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp`. Consider the case `cons p w ih`. Establish `hp` using `hw p (by simp)`. Establish `ih'` using `ih (fun q hq => hw q (by simp [hq]))`.

Simplify using `only [List.map_cons, List.sum_cons]`. Rewrite using `[show ∀ u v : Wt n, ν + (u + v) = (ν + v) + u from fun u v => by abel, dot_add, dot_rt]`. Use `hx hp.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem maj_word {n : ℕ} (ν x : Wt n) (hx : Antitone x) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, p.2 < p.1) :
    ∑ a, x a * (ν + (w.map fun p => rt p.1 p.2).sum) a ≤ ∑ a, x a * ν a := by
  induction w with
  | nil => simp
  | cons p w ih =>
    have hp := hw p (by simp)
    have ih' := ih (fun q hq => hw q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons]
    rw [show ∀ u v : Wt n, ν + (u + v) = (ν + v) + u from fun u v => by abel, dot_add, dot_rt]
    have := hx hp.le
    linarith

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [Formalism.REAL.rhoC, rhoV]`. Simplify using `only [and_true, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]`. Establish `ha` using `a.isLt`. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem rhoC_true (n : ℕ) : Formalism.REAL.rhoC (fun _ : Fin n => true) = rhoV n := by
  funext a
  simp only [Formalism.REAL.rhoC, rhoV]
  simp only [and_true, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  have ha := a.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/- English proof (translation)
Simplify using `[Formalism.REAL.nsq, Formalism.REAL.dot, nsq, sq]`.
-/
private theorem nsq_eq {n : ℕ} (u : Fin n → ℝ) : Formalism.REAL.nsq u = nsq u := by
  simp [Formalism.REAL.nsq, Formalism.REAL.dot, nsq, sq]

/- English proof (translation)
Introduce `a b hab`. Establish `: ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Simplify using `only [rhoV]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem rhoV_anti (n : ℕ) : Antitone (rhoV n) := by
  intro a b hab
  have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [rhoV]
  linarith

/- English proof (translation)
Introduce `n V _ _ F hF S hS hst ν hν`. Establish `hK : Formalism.REAL.KRel (fun _ : Fin n => true) F` using `Formalism.REAL.glRel_kRel _ F hF.gl`. Establish `hU : Formalism.REAL.KUnit (fun _ : Fin n => true) F` using `fun a b _ x y => hF.unit a b x y`. Establish `hSt : Formalism.REAL.KStable (fun _ : Fin n => true) F S` using `fun a b _ x hx => hst a b x hx`. Take `⟨m, x, μ, hx, horth, hsup⟩` from `Formalism.REAL.kDecomp V n (fun _ => true) F S hS hK hU hSt`.

Establish `hμ : ∀ i, μ i = ν`. Introduce `i`. Assume the negation of the conclusion as `h`. Establish `h0` using `hν (μ i) h`. Establish `hi : x i ∈ hw F (μ i) ⊓ S` using `Submodule.mem_inf.mpr ⟨(hx i).2.2, (hx i).1⟩`.

Rewrite `hi` using `[h0]`. Conclude with `(hx i).2.1 ((Submodule.mem_bot ℂ).mp hi)`. Establish `hC : ∀ y ∈ S, Cas F y = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • y`. Establish `hCas : Formalism.REAL.CasK (fun _ : Fin n => true) F = Cas F`. Simplify using `[Formalism.REAL.CasK, Formalism.REAL.Cas]`.

Establish `hck : Formalism.REAL.ckv (fun _ : Fin n => true) ν = nsq (ν + rhoV n) - nsq (rhoV n)`. Simplify using `only [Formalism.REAL.ckv, rhoC_true, nsq_eq]`. Introduce `y hy`. Rewrite `hy` using `[← hsup]`. Use `Submodule.iSup_induction _ (motive := fun y => Cas F y = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • y) hy ?_ ?_ ?_` and prove the remaining obligations.

Introduce `i z hz`. Establish `hz'` using `Formalism.REAL.kCasSpan V n _ F (μ i) (x i) hK (hx i).2.2 z hz`. Rewrite `hz'` using `[hCas, hμ i, hck]`. Conclude with `hz'`. Simplify using the standard rewrite rules.

Introduce `a b ha hb`. Rewrite using `[map_add, ha, hb, smul_add]`. Establish `hM : ∀ μ', wsp F μ' ⊓ S ≠ ⊥ → Maj μ' ν`. Introduce `μ' hne`. Assume the negation of the conclusion as `hnot`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Take `⟨hyw, hyS⟩` from `Submodule.mem_inf.mp hy`. Rewrite using `[Submodule.mem_bot]`.

Establish `hle : S ≤ LinearMap.ker (innerₛₗ ℂ y)`. Rewrite using `[← hsup]`. Apply `iSup_le` to reduce the goal to its premises. Introduce `i`. Rewrite using `[(Formalism.REAL.kLow V n _ F (μ i) (x i) hK (hx i).2.2).1, Formalism.REAL.lowSpan, Submodule.span_le]`.

Introduce and unpack `z ⟨w, hwl, rfl⟩`. Establish `hwt` using `wt_word hF.gl (hx i).2.2.1 w`. Rewrite `hwt` using `[hμ i]`. Establish `hne' : μ' ≠ ν + (w.map fun p => rt p.1 p.2).sum`. Introduce and unpack `rfl`.

Conclude with `hnot (fun t ht => maj_word ν t ht w (fun p hp => (hwl p hp).2))`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]`. Conclude with `Formalism.REAL.kWtOrth V n _ F μ' _ y _ hU hyw hwt hne'`. Establish `h0` using `hle hyS`. Rewrite `h0` using `[LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero]`.

Conclude with `h0`. Use `⟨hC, hM, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Take `⟨hyw, hyS⟩` from `Submodule.mem_inf.mp hy`.

Establish `hk : KHighest (fun _ : Fin n => true) F ν y`. Use `⟨hyw, ?_⟩` and prove the remaining obligations. Introduce `a b hab _`. Assume the negation of the conclusion as `hne`. Establish `hmem : F a b y ∈ wsp F (ν + rt a b) ⊓ S` using `Submodule.mem_inf.mpr ⟨wt_shift hF.gl hyw a b, hst a b y hyS⟩`.

Establish `hM'` using `hM (ν + rt a b) (by`. Introduce `h`. Rewrite `hmem` using `[h]`. Conclude with `hne ((Submodule.mem_bot ℂ).mp hmem))`. Establish `h1` using `hM' (rhoV n) (rhoV_anti n)`.

Rewrite `h1` using `[dot_add, dot_rt]`. Establish `hlt : (a : ℝ) < (b : ℝ)` using `by exact_mod_cast hab`. Establish `h2 : rhoV n b < rhoV n a`. Simplify using `only [rhoV]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Submodule.mem_inf.mpr ⟨hk, hyS⟩`. Introduce `y hy`. Take `⟨h1, h2⟩` from `Submodule.mem_inf.mp hy`. Conclude with `Submodule.mem_inf.mpr ⟨(show KHighest (fun _ : Fin n => true) F ν y from h1).1, h2⟩`.
-/
theorem UpperTheory.RealTr.isoFacts :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ ν : Wt n, (∀ μ, μ ≠ ν → hw F μ ⊓ S = ⊥) →
      (∀ x ∈ S, Cas F x = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • x) ∧ (∀ μ, wsp F μ ⊓ S ≠ ⊥ → Maj μ ν) ∧ wsp F ν ⊓ S = hw F ν ⊓ S := by
  intro n V _ _ F hF S hS hst ν hν
  have hK : Formalism.REAL.KRel (fun _ : Fin n => true) F := Formalism.REAL.glRel_kRel _ F hF.gl
  have hU : Formalism.REAL.KUnit (fun _ : Fin n => true) F := fun a b _ x y => hF.unit a b x y
  have hSt : Formalism.REAL.KStable (fun _ : Fin n => true) F S := fun a b _ x hx => hst a b x hx
  obtain ⟨m, x, μ, hx, horth, hsup⟩ := Formalism.REAL.kDecomp V n (fun _ => true) F S hS hK hU hSt
  have hμ : ∀ i, μ i = ν := by
    intro i
    by_contra h
    have h0 := hν (μ i) h
    have hi : x i ∈ hw F (μ i) ⊓ S := Submodule.mem_inf.mpr ⟨(hx i).2.2, (hx i).1⟩
    rw [h0] at hi
    exact (hx i).2.1 ((Submodule.mem_bot ℂ).mp hi)
  have hC : ∀ y ∈ S, Cas F y = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • y := by
    have hCas : Formalism.REAL.CasK (fun _ : Fin n => true) F = Cas F := by
      simp [Formalism.REAL.CasK, Formalism.REAL.Cas]
    have hck : Formalism.REAL.ckv (fun _ : Fin n => true) ν = nsq (ν + rhoV n) - nsq (rhoV n) := by
      simp only [Formalism.REAL.ckv, rhoC_true, nsq_eq]
    intro y hy
    rw [← hsup] at hy
    refine Submodule.iSup_induction _ (motive := fun y => Cas F y = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • y) hy ?_ ?_ ?_
    · intro i z hz
      have hz' := Formalism.REAL.kCasSpan V n _ F (μ i) (x i) hK (hx i).2.2 z hz
      rw [hCas, hμ i, hck] at hz'
      exact hz'
    · simp
    · intro a b ha hb
      rw [map_add, ha, hb, smul_add]
  have hM : ∀ μ', wsp F μ' ⊓ S ≠ ⊥ → Maj μ' ν := by
    intro μ' hne
    by_contra hnot
    apply hne
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
    rw [Submodule.mem_bot]
    have hle : S ≤ LinearMap.ker (innerₛₗ ℂ y) := by
      rw [← hsup]
      apply iSup_le
      intro i
      rw [(Formalism.REAL.kLow V n _ F (μ i) (x i) hK (hx i).2.2).1, Formalism.REAL.lowSpan, Submodule.span_le]
      rintro z ⟨w, hwl, rfl⟩
      have hwt := wt_word hF.gl (hx i).2.2.1 w
      rw [hμ i] at hwt
      have hne' : μ' ≠ ν + (w.map fun p => rt p.1 p.2).sum := by
        rintro rfl
        exact hnot (fun t ht => maj_word ν t ht w (fun p hp => (hwl p hp).2))
      simp only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]
      exact Formalism.REAL.kWtOrth V n _ F μ' _ y _ hU hyw hwt hne'
    have h0 := hle hyS
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at h0
    exact h0
  refine ⟨hC, hM, ?_⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
    have hk : KHighest (fun _ : Fin n => true) F ν y := by
      refine ⟨hyw, ?_⟩
      intro a b hab _
      by_contra hne
      have hmem : F a b y ∈ wsp F (ν + rt a b) ⊓ S :=
        Submodule.mem_inf.mpr ⟨wt_shift hF.gl hyw a b, hst a b y hyS⟩
      have hM' := hM (ν + rt a b) (by
        intro h
        rw [h] at hmem
        exact hne ((Submodule.mem_bot ℂ).mp hmem))
      have h1 := hM' (rhoV n) (rhoV_anti n)
      rw [dot_add, dot_rt] at h1
      have hlt : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
      have h2 : rhoV n b < rhoV n a := by
        simp only [rhoV]
        linarith
      linarith
    exact Submodule.mem_inf.mpr ⟨hk, hyS⟩
  · intro y hy
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hy
    exact Submodule.mem_inf.mpr ⟨(show KHighest (fun _ : Fin n => true) F ν y from h1).1, h2⟩
