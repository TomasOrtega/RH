import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBActSgDDiamIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwistStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorUpperULCommuteScaleOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondActionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatio
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongr

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.ThNHecke

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

/- English proof (translation)
Establish `hcop : Nat.Coprime q l` using `(Nat.coprime_primes hq hl).mpr hql`. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.mpr hcop`. Establish `e : (u : Ω) * (q : Ω) + (v : Ω) * (l : Ω) = 1` using `by exact_mod_cast congrArg (fun t : ℤ => (t : Ω)) huv`. Establish `hu : A.valuation (u : Ω) ≤ 1` using `(A.valuation_le_one_iff _).mpr (intCast_mem A u)`. Establish `hv : A.valuation (v : Ω) ≤ 1` using `(A.valuation_le_one_iff _).mpr (intCast_mem A v)`.

Establish `hqle : A.valuation (q : Ω) ≤ 1` using `(A.valuation_le_one_iff _).mpr (natCast_mem A q)`. Establish `hl1 : A.valuation (l : Ω) < 1` using `(A.mem_nonunits_iff).mp hlA`. Establish `hq1 : A.valuation (q : Ω) = 1`. Use `le_antisymm hqle (not_lt.mp fun hlt => ?_)` and prove the remaining obligations. Establish `h1 : A.valuation ((u : Ω) * (q : Ω)) < 1`.

Rewrite using `[map_mul]; exact (mul_le_mul' hu le_rfl).trans_lt (by rwa [one_mul])`. Establish `h2 : A.valuation ((v : Ω) * (l : Ω)) < 1`. Rewrite using `[map_mul]; exact (mul_le_mul' hv le_rfl).trans_lt (by rwa [one_mul])`. Establish `h3` using `Valuation.map_add_lt A.valuation h1 h2`. Rewrite `h3` using `[e, map_one]`.

Conclude with `lt_irrefl _ h3`. Rewrite using `[← A.valuation_le_one_iff, map_inv₀, hq1, inv_one]`.
-/
theorem inv_natCast_mem (A : ValuationSubring Ω) {l q : ℕ} (hq : q.Prime) (hl : l.Prime) (hql : q ≠ l)
    (hlA : (l : Ω) ∈ A.nonunits) : ((q : Ω))⁻¹ ∈ A := by
  have hcop : Nat.Coprime q l := (Nat.coprime_primes hq hl).mpr hql
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have e : (u : Ω) * (q : Ω) + (v : Ω) * (l : Ω) = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : Ω)) huv
  have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A u)
  have hv : A.valuation (v : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A v)
  have hqle : A.valuation (q : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A q)
  have hl1 : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).mp hlA
  have hq1 : A.valuation (q : Ω) = 1 := by
    refine le_antisymm hqle (not_lt.mp fun hlt => ?_)
    have h1 : A.valuation ((u : Ω) * (q : Ω)) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hu le_rfl).trans_lt (by rwa [one_mul])
    have h2 : A.valuation ((v : Ω) * (l : Ω)) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hv le_rfl).trans_lt (by rwa [one_mul])
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [e, map_one] at h3
    exact lt_irrefl _ h3
  rw [← A.valuation_le_one_iff, map_inv₀, hq1, inv_one]

/- English proof (translation)
Take `⟨φ, h1, h2⟩` from `hj`. Establish `hA` using `(GlobalTheory.T.modular_function_tower_integrality ε X ε.injective ⟨φ, h2, h1⟩ l).1`. Establish `hNl : Nat.Coprime N l` using `Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).mpr hlN)`. Establish `hle : X.B N l w ≤ (X.B N l w).comap (X.op N l T)` using `Submodule.span_le.mpr (fun x hx => Submodule.subset_span (StabHecke.op_BSet X hA N w (by omega) hNl T hT x hx))`. Conclude with `hle hb`.
-/
theorem op_mem_B [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (N l w : ℕ) [Fact l.Prime]
    (hN : 1 ≤ N) (hlN : ¬ l ∣ N) (T : Letter) (hT : admitted N l T) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.op N l T b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := hj
  have hA := (GlobalTheory.T.modular_function_tower_integrality ε X ε.injective ⟨φ, h2, h1⟩ l).1
  have hNl : Nat.Coprime N l :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).mpr hlN)
  have hle : X.B N l w ≤ (X.B N l w).comap (X.op N l T) :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span
      (StabHecke.op_BSet X hA N w (by omega) hNl T hT x hx))
  exact hle hb

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Take `⟨f, hfI, hfc, hfδ, hfD⟩` from `h1`. Take `⟨f', hf'I, hf'c, hf'δ, hf'D⟩` from `h2`. Take `⟨u, hu⟩` from `GlobalTheory.Tower.cls_eq_pow X l n f f' (hfc.symm.trans hf'c)`. Establish `hf0 : (f : X.K) ≠ 0` using `f.ne_zero`.

Establish `hu0 : (u : X.K) ≠ 0` using `u.ne_zero`. Establish `hL : (u : X.K) ^ (l ^ n) = (f : X.K)⁻¹ * f'` using `by rw [hu]; field_simp`. Establish `hT` using `GlobalTheory.TInv.sl_T_eq X N l n hl.out l2 hN hN1 (u : X.K) hu0 (by`. Introduce `γ hγ; rw [hL, map_mul, map_inv₀, hfI γ hγ, hf'I γ hγ]) (by`. Introduce `δ hδ hδ'`.

Take `⟨g, hgI, hg⟩` from `hfδ δ hδ hδ'`. Take `⟨g', hg'I, hg'⟩` from `hf'δ δ hδ hδ'`. Establish `hsf : X.sl (ofSL δ) (f : X.K) ≠ 0`. Introduce `h0`. Conclude with `hf0 ((X.sl (ofSL δ)).injective (h0.trans (map_zero _).symm))`.

Establish `hg0 : g ≠ 0`. Introduce `h0`. Rewrite `hg` using `[h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]`. Conclude with `mul_ne_zero hf0 hsf hg`. Use `⟨g' / g, ?_, ?_⟩` and prove the remaining obligations.

Introduce `γ hγ`. Rewrite using `[map_div₀, hgI γ hγ, hg'I γ hγ]`. Rewrite using `[div_pow, ← hg', ← hg, hu, map_mul, map_pow]`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`.

Conclude with `GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong X A l hlA n (f : X.K) (u : X.K) hf0 hu0 hT φ φ' hfD (by rw [← hu]; exact hf'D)`.
-/
theorem isThB_cong [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [hl : Fact l.Prime]
    (l2 : l ≠ 2) (hN : ¬ l ∣ N) (hN1 : 1 ≤ N) (hlA : (l : Ω) ∈ A.nonunits) (n : ℕ) (b : X.Fn l)
    (φ φ' : HahnSeries ℚ Ω) (h1 : IsThB X A N l n b φ) (h2 : IsThB X A N l n b φ') :
    ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨f, hfI, hfc, hfδ, hfD⟩ := h1
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h2
  obtain ⟨u, hu⟩ := GlobalTheory.Tower.cls_eq_pow X l n f f' (hfc.symm.trans hf'c)
  have hf0 : (f : X.K) ≠ 0 := f.ne_zero
  have hu0 : (u : X.K) ≠ 0 := u.ne_zero
  have hL : (u : X.K) ^ (l ^ n) = (f : X.K)⁻¹ * f' := by rw [hu]; field_simp
  have hT := GlobalTheory.TInv.sl_T_eq X N l n hl.out l2 hN hN1 (u : X.K) hu0 (by
      intro γ hγ; rw [hL, map_mul, map_inv₀, hfI γ hγ, hf'I γ hγ]) (by
      intro δ hδ hδ'
      obtain ⟨g, hgI, hg⟩ := hfδ δ hδ hδ'
      obtain ⟨g', hg'I, hg'⟩ := hf'δ δ hδ hδ'
      have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := by
        intro h0; exact hf0 ((X.sl (ofSL δ)).injective (h0.trans (map_zero _).symm))
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hg; exact mul_ne_zero hf0 hsf hg
      refine ⟨g' / g, ?_, ?_⟩
      · intro γ hγ; rw [map_div₀, hgI γ hγ, hg'I γ hγ]
      · rw [div_pow, ← hg', ← hg, hu, map_mul, map_pow]; field_simp; ring)
  exact GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong X A l hlA n (f : X.K) (u : X.K) hf0 hu0 hT φ φ' hfD (by rw [← hu]; exact hf'D)

end GlobalTheory.ThNHecke

open GlobalTheory.ThNHecke in

/- English proof (translation)
Introduce `Ω _ _ _ ε X A N l _ hj hl2 hlN hN hlA n w d hw hd b hb`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Establish `halg : Algebra.IsAlgebraic ℚ Ω` using `IsAlgClosure.isAlgebraic`. Establish `hl : l.Prime` using `Fact.out`. Establish `stab : ∀ T : Letter, admitted N l T → ∀ c : X.Fn l, c ∈ X.B N l w → X.op N l T c ∈ X.B N l w` using `fun T hT c hc => op_mem_B ε X hj N l w (by omega) hlN T hT c hc`.

Establish `dB : ∀ e : ℕ, e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w → X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c ∈ X.B N l w` using `fun e he c hc => stab (Letter.D e) he c hc`. Establish `exL : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w → IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) ∧ IsLat 1 (thN X A N l m e c)` using `fun m e he c hc => GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l hj hl2 hlN (by omega) hlA m w e hw he c hc`. Establish `ex : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w → IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c)` using `fun m e he c hc => (exL m e he c hc).1`. Establish `uniq : ∀ (m : ℕ) (c : X.Fn l), c ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω, IsThB X A N l m c φ → IsThB X A N l m c φ' → ∀ r, CgA A l m (φ.coeff r) (φ'.coeff r)` using `fun m c _ φ φ' h h' => isThB_cong X A N l hl2 hlN (by omega) hlA m c φ φ' h h'`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `q hqP hqd r`. Establish `hqN : q.Coprime N` using `(Nat.Prime.coprime_iff_not_dvd hqP).mpr (fun h => hqd (dvd_mul_of_dvd_left h l))`. Establish `hql : q ≠ l`. Introduce and unpack `rfl`. Conclude with `hqd (dvd_mul_left q N)`.

Establish `hqinv` using `inv_natCast_mem A hqP hl hql hlA`. Establish `hTb : X.heckeT N l q b ∈ X.B N l w` using `stab (Letter.T q) ⟨hqP, hqd⟩ b hb`. Establish `e1` using `exL n d hd b hb`. Establish `e2` using `exL n (d * q) (Nat.Coprime.mul hd hqN) b hb`. Establish `h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b)) (hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b))` using `GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist Ω ε X A N l halg hj (by omega) n w d q hw hqP hqd hqinv hlA hl2 hlN hd b hb _ _ e1.2 e2.2 e1.1 e2.1`.

Conclude with `uniq n _ (dB d hd _ hTb) _ _ (ex n d hd _ hTb) h2 r`. Introduce `r`. Establish `hUb : X.heckeU l b ∈ X.B N l w` using `stab Letter.U trivial b hb`. Establish `e1` using `exL (n + 1) d hd b hb`. Establish `h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (uq l (thN X A N l (n + 1) d b))` using `GlobalTheory.T.thetaOperator_upperU_l_commute_scale_one Ω ε X A N l n w d halg hj hl2 (by omega) hw hlA hd hlN b hb _ e1.2 e1.1`.

Conclude with `uniq n _ (dB d hd _ hUb) _ _ (ex n d hd _ hUb) h2 r`. Introduce `a ha r`. Establish `hDb : X.diam N l a b ∈ X.B N l w` using `stab (Letter.D a) ha b hb`. Establish `h1` using `(GlobalTheory.KZ.isThB_act_sgD_diam_iff Ω ε X A N l n w a d ha hd b hb _).mp (ex n d hd _ hDb)`. Conclude with `uniq n _ (dB (d * a) (Nat.Coprime.mul hd ha) b hb) _ _ h1 (ex n (d * a) (Nat.Coprime.mul hd ha) b hb) r`.
-/
theorem GlobalTheory.CyclotomicQExpansion.thN_hecke : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ∀ r, CgA A l n ((thN X A N l n d (X.heckeT N l q b)).coeff r)
      ((hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)).coeff r)) ∧
  (∀ r, CgA A l n ((thN X A N l n d (X.heckeU l b)).coeff r) ((uq l (thN X A N l (n + 1) d b)).coeff r)) ∧
  (∀ a : ℕ, a.Coprime N → ∀ r, CgA A l n ((thN X A N l n d (X.diam N l a b)).coeff r) ((thN X A N l n (d * a) b).coeff r)) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN hlA n w d hw hd b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl : l.Prime := Fact.out
  have stab : ∀ T : Letter, admitted N l T → ∀ c : X.Fn l, c ∈ X.B N l w → X.op N l T c ∈ X.B N l w :=
    fun T hT c hc => op_mem_B ε X hj N l w (by omega) hlN T hT c hc
  have dB : ∀ e : ℕ, e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c ∈ X.B N l w :=
    fun e he c hc => stab (Letter.D e) he c hc
  have exL : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) ∧ IsLat 1 (thN X A N l m e c) :=
    fun m e he c hc => GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l hj hl2 hlN (by omega) hlA m w e hw he c hc
  have ex : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) :=
    fun m e he c hc => (exL m e he c hc).1
  have uniq : ∀ (m : ℕ) (c : X.Fn l), c ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω,
      IsThB X A N l m c φ → IsThB X A N l m c φ' → ∀ r, CgA A l m (φ.coeff r) (φ'.coeff r) :=
    fun m c _ φ φ' h h' => isThB_cong X A N l hl2 hlN (by omega) hlA m c φ φ' h h'
  refine ⟨?_, ?_, ?_⟩
  · intro q hqP hqd r
    have hqN : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hqP).mpr (fun h => hqd (dvd_mul_of_dvd_left h l))
    have hql : q ≠ l := by
      rintro rfl; exact hqd (dvd_mul_left q N)
    have hqinv := inv_natCast_mem A hqP hl hql hlA
    have hTb : X.heckeT N l q b ∈ X.B N l w := stab (Letter.T q) ⟨hqP, hqd⟩ b hb
    have e1 := exL n d hd b hb
    have e2 := exL n (d * q) (Nat.Coprime.mul hd hqN) b hb
    have h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b))
        (hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)) :=
      GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist Ω ε X A N l halg hj (by omega) n w d q hw hqP hqd hqinv hlA hl2 hlN hd b hb _ _ e1.2 e2.2 e1.1 e2.1
    exact uniq n _ (dB d hd _ hTb) _ _ (ex n d hd _ hTb) h2 r
  · intro r
    have hUb : X.heckeU l b ∈ X.B N l w := stab Letter.U trivial b hb
    have e1 := exL (n + 1) d hd b hb
    have h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b))
        (uq l (thN X A N l (n + 1) d b)) :=
      GlobalTheory.T.thetaOperator_upperU_l_commute_scale_one Ω ε X A N l n w d halg hj hl2 (by omega) hw hlA hd hlN b hb _ e1.2 e1.1
    exact uniq n _ (dB d hd _ hUb) _ _ (ex n d hd _ hUb) h2 r
  · intro a ha r
    have hDb : X.diam N l a b ∈ X.B N l w := stab (Letter.D a) ha b hb
    have h1 := (GlobalTheory.KZ.isThB_act_sgD_diam_iff Ω ε X A N l n w a d ha hd b hb _).mp (ex n d hd _ hDb)
    exact uniq n _ (dB (d * a) (Nat.Coprime.mul hd ha) b hb) _ _ h1 (ex n (d * a) (Nat.Coprime.mul hd ha) b hb) r
