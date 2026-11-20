import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamGeoEqFormula

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ForcedWeights

section Chain

variable {R : Ranks} (P : HCParam R)

/- English proof (translation)
The claim follows from `(P.u_gt_v ⟨i + 1, h⟩).trans (P.v_gt_u ⟨i, by omega⟩)`.
-/
lemma v_step (i : ℕ) (h : i + 1 < R.k - 1) : P.v ⟨i + 1, h⟩ < P.v ⟨i, by omega⟩ :=
  (P.u_gt_v ⟨i + 1, h⟩).trans (P.v_gt_u ⟨i, by omega⟩)

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => exact v_step P i h`. Consider the case `succ d ih => exact (v_step P (i + d + 1) h).trans (ih (by omega))`.
-/
lemma v_lt (i d : ℕ) (h : i + d + 1 < R.k - 1) : P.v ⟨i + d + 1, h⟩ < P.v ⟨i, by omega⟩ := by
  induction d with
  | zero => exact v_step P i h
  | succ d ih => exact (v_step P (i + d + 1) h).trans (ih (by omega))

/- English proof (translation)
Introduce and unpack `⟨i, hi⟩ ⟨j, hj⟩ hij`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt (show i < j from hij)`. Conclude with `v_lt P i d hj`.
-/
lemma v_strictAnti : StrictAnti P.v := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show i < j from hij)
  exact v_lt P i d hj

/- English proof (translation)
Establish `ht : (0 : ℚ) ≤ R.t` using `by positivity`. Proceed by induction on `d with`. Consider the case `zero => have := P.gap_eb ⟨i, by omega⟩ h; simp only [add_zero] at *; linarith`. Consider the case `succ d ih`. Establish `h1` using `ih (by omega)`.

Establish `h2` using `P.gap_be ⟨i + d + 1, by omega⟩`. Establish `h3 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨i + (d + 1) + 1, h⟩ - P.e ⟨i + d + 1, by omega⟩` using `P.gap_eb ⟨i + d + 1, by omega⟩ h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma hcParameter_e_add_halfShift_le_b_succ (i d : ℕ) (h : i + d + 1 < R.m) :
    P.e ⟨i, by omega⟩ + ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨i + d + 1, h⟩ := by
  have ht : (0 : ℚ) ≤ R.t := by positivity
  induction d with
  | zero => have := P.gap_eb ⟨i, by omega⟩ h; simp only [add_zero] at *; linarith
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 := P.gap_be ⟨i + d + 1, by omega⟩
    have h3 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨i + (d + 1) + 1, h⟩ - P.e ⟨i + d + 1, by omega⟩ :=
      P.gap_eb ⟨i + d + 1, by omega⟩ h
    linarith

/- English proof (translation)
Take `⟨i, hi⟩` from `i`. Take `⟨j, hj⟩` from `j`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt (show i < j from hij)`. Conclude with `hcParameter_e_add_halfShift_le_b_succ P i d hj`.
-/
lemma eb {i j : Fin R.m} (hij : i < j) : P.e i + ((R.t : ℚ) + 3) / 2 ≤ P.b j := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show i < j from hij)
  exact hcParameter_e_add_halfShift_le_b_succ P i d hj

/- English proof (translation)
Introduce `i j hij`. Establish `ht : (0 : ℚ) ≤ R.t` using `by positivity`. Use `eb P hij` as an intermediate fact. Use `P.gap_be i` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma b_strictMono : StrictMono P.b := by
  intro i j hij
  have ht : (0 : ℚ) ≤ R.t := by positivity
  have := eb P hij
  have := P.gap_be i
  linarith

/- English proof (translation)
Use `(b_strictMono P).monotone hij` as an intermediate fact. Use `P.gap_be j` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma be {i j : Fin R.m} (hij : i ≤ j) : P.b i + ((R.t : ℚ) + 3) / 2 ≤ P.e j := by
  have := (b_strictMono P).monotone hij
  have := P.gap_be j
  linarith

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hm` using `R.two_le_m`. Establish `h1` using `P.u_last_gt (by omega) (by omega)`. Establish `h2` using `P.v_gt_u ⟨R.k - 2, by omega⟩`. Establish `h3 : P.v ⟨R.k - 2, by omega⟩ ≤ P.v i` using `(v_strictAnti P).antitone (by rw [Fin.le_def]; have := i.2; simp only; omega)`.

Establish `h4 : P.b ⟨0, by omega⟩ ≤ P.b j` using `(b_strictMono P).monotone (by rw [Fin.le_def]; simp)`. Establish `h5 : P.u ⟨R.k - 1, by omega⟩ = P.u ⟨R.k - 2 + 1, by omega⟩`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Simplify using `only at h2`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma negb_lt_v (i : Fin (R.k - 1)) (j : Fin R.m) : -P.b j < P.v i := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 := P.u_last_gt (by omega) (by omega)
  have h2 := P.v_gt_u ⟨R.k - 2, by omega⟩
  have h3 : P.v ⟨R.k - 2, by omega⟩ ≤ P.v i :=
    (v_strictAnti P).antitone (by rw [Fin.le_def]; have := i.2; simp only; omega)
  have h4 : P.b ⟨0, by omega⟩ ≤ P.b j := (b_strictMono P).monotone (by rw [Fin.le_def]; simp)
  have h5 : P.u ⟨R.k - 1, by omega⟩ = P.u ⟨R.k - 2 + 1, by omega⟩ := by
    congr 2; omega
  simp only at h2
  linarith

def entry : Fin (R.k - 1) ⊕ Fin R.m ⊕ (Fin R.m × Fin R.t) → ℚ
  | .inl i => P.v i
  | .inr (.inl i) => -P.b i
  | .inr (.inr (i, a)) => -P.e i + ((R.t : ℚ) - 1) / 2 - ((a : ℕ) : ℚ)

/- English proof (translation)
Assemble the required witnesses or components as `⟨by positivity, by exact_mod_cast a.2⟩`.
-/
lemma fin_bounds (a : Fin R.t) : (0 : ℚ) ≤ ((a : ℕ) : ℚ) ∧ ((a : ℕ) : ℚ) + 1 ≤ R.t :=
  ⟨by positivity, by exact_mod_cast a.2⟩

/- English proof (translation)
Use `negb_lt_v P i j` as an intermediate fact. Use `P.gap_be j` as an intermediate fact. Use `fin_bounds a` as an intermediate fact. Introduce `h`. Combine the linear relations using `[this.1]`.
-/
lemma entry_ne_vblock (i : Fin (R.k - 1)) (j : Fin R.m) (a : Fin R.t) :
    P.v i ≠ -P.e j + ((R.t : ℚ) - 1) / 2 - ((a : ℕ) : ℚ) := by
  have := negb_lt_v P i j
  have := P.gap_be j
  have := fin_bounds a
  intro h
  linarith [this.1]

/- English proof (translation)
Take `⟨h0, h1⟩` from `fin_bounds a`. Introduce `h`. Break down `le_or_gt i j with hij | hij` into its components or cases. Use `be P hij` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `eb P hij` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma entry_ne_bblock (i j : Fin R.m) (a : Fin R.t) :
    -P.b i ≠ -P.e j + ((R.t : ℚ) - 1) / 2 - ((a : ℕ) : ℚ) := by
  obtain ⟨h0, h1⟩ := fin_bounds a
  intro h
  rcases le_or_gt i j with hij | hij
  · have := be P hij; linarith
  · have := eb P hij; linarith

/- English proof (translation)
Apply the tactic sequence `rintro (i | i | ⟨i, a⟩) (j | j | ⟨j, b⟩) h <;> simp only [entry] at h`. Rewrite using `[(v_strictAnti P).injective h]`. Conclude with `absurd h (negb_lt_v P i j).ne'`. Conclude with `absurd h (entry_ne_vblock P i j b)`. Conclude with `absurd h (negb_lt_v P j i).ne`.

Rewrite using `[(b_strictMono P).injective (neg_injective h)]`. Conclude with `absurd h (entry_ne_bblock P i j b)`. Conclude with `absurd h.symm (entry_ne_vblock P j i a)`. Conclude with `absurd h.symm (entry_ne_bblock P j i a)`. Take `⟨a0, a1⟩` from `fin_bounds a`.

Take `⟨b0, b1⟩` from `fin_bounds b`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Use `eb P hij` as an intermediate fact. Use `P.gap_be j` as an intermediate fact. It suffices to derive a contradiction.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h' : ((a : ℕ) : ℚ) = ((b : ℕ) : ℚ)` using `by linarith`. Establish `h'' : a = b` using `Fin.ext (by exact_mod_cast h')`. Rewrite using `[h'']`. Use `eb P hij` as an intermediate fact.

Use `P.gap_be i` as an intermediate fact. It suffices to derive a contradiction. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma entry_injective : Function.Injective (entry P) := by
  rintro (i | i | ⟨i, a⟩) (j | j | ⟨j, b⟩) h <;> simp only [entry] at h
  · rw [(v_strictAnti P).injective h]
  · exact absurd h (negb_lt_v P i j).ne'
  · exact absurd h (entry_ne_vblock P i j b)
  · exact absurd h (negb_lt_v P j i).ne
  · rw [(b_strictMono P).injective (neg_injective h)]
  · exact absurd h (entry_ne_bblock P i j b)
  · exact absurd h.symm (entry_ne_vblock P j i a)
  · exact absurd h.symm (entry_ne_bblock P j i a)
  · obtain ⟨a0, a1⟩ := fin_bounds a
    obtain ⟨b0, b1⟩ := fin_bounds b
    rcases lt_trichotomy i j with hij | rfl | hij
    · have := eb P hij; have := P.gap_be j; exfalso; linarith
    · have h' : ((a : ℕ) : ℚ) = ((b : ℕ) : ℚ) := by linarith
      have h'' : a = b := Fin.ext (by exact_mod_cast h')
      rw [h'']
    · have := eb P hij; have := P.gap_be i; exfalso; linarith

/- English proof (translation)
Break down `x with i | i | ⟨i, a⟩` into its components or cases. Conclude with `P.v_int i`. Take `⟨z, hz⟩` from `P.b_int i`. Conclude with `⟨-z, by simp [entry, hz]⟩`. Take `⟨z, hz⟩` from `P.e_int i`.

Take `⟨s, hs⟩` from `R.t_odd`. Use `⟨-z + s - (a : ℕ), ?_⟩` and prove the remaining obligations. Establish `: (R.t : ℚ) = 2 * s + 1` using `by exact_mod_cast hs`. Simplify using `only [entry, hz, this]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma entry_int (x) : ∃ z : ℤ, entry P x = z := by
  rcases x with i | i | ⟨i, a⟩
  · exact P.v_int i
  · obtain ⟨z, hz⟩ := P.b_int i
    exact ⟨-z, by simp [entry, hz]⟩
  · obtain ⟨z, hz⟩ := P.e_int i
    obtain ⟨s, hs⟩ := R.t_odd
    refine ⟨-z + s - (a : ℕ), ?_⟩
    have : (R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
    simp only [entry, hz, this]
    push_cast
    ring

end Chain

/- English proof (translation)
Take `⟨s, rfl⟩` from `hodd`. Establish `hT : (Finset.univ.image f).card = 2 * s + 1`. Rewrite using `[Finset.card_image_of_injective _ hf, Finset.card_univ, hN]`. Set `c : Fin (2 * s + 1) → ℚ` to `fun i => (Finset.univ.image f).orderEmbOfFin hT i.rev`. Establish `hc : StrictAnti c` using `fun i j hij => ((Finset.univ.image f).orderEmbOfFin hT).strictMono (Fin.rev_lt_rev.mpr hij)`.

Establish `hmem : ∀ i, ∃ x, f x = c i` using `fun i => by`. Use `(Finset.univ.image f).orderEmbOfFin_mem hT i.rev` as an intermediate fact. Take `⟨x, -, hx⟩` from `Finset.mem_image.mp this`. Conclude with `⟨x, hx⟩`. Establish `hci : ∀ i, ∃ z : ℤ, c i = z` using `fun i => by`.

Take `⟨x, hx⟩` from `hmem i`. Rewrite using `[← hx]`. Conclude with `hz x`. Use `choose z hzc using hci`. Use `⟨⟨fun i => z i - s + (i : ℕ), ?_⟩, ?_, c, hc, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fin.antitone_iff_succ_le]`. Introduce `i`. Establish `h1` using `hc (Fin.castSucc_lt_succ (i := i))`. Rewrite `h1` using `[hzc, hzc]`. Establish `h2 : z i.succ < z i.castSucc` using `by exact_mod_cast h1`.

Simplify using `only [Fin.val_succ, Fin.val_castSucc]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.card_image_of_injective _ (fun x y h => hf (Prod.ext_iff.mp h).1), Finset.card_univ, hN]`. Introduce `i`.

Take `⟨x, hx⟩` from `hmem i`. Conclude with `⟨true, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by rw [hx]⟩⟩`. Introduce `i`. Simplify using `only [rhoVec, hzc]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma exists_isWtOfPar {ι : Type} [Fintype ι] (f : ι → ℚ) (hf : Function.Injective f)
    (hz : ∀ x, ∃ z : ℤ, f x = z) {N : ℕ} (hN : Fintype.card ι = N) (hodd : Odd N) :
    ∃ lam : DomWeight N, Bridge.IsWtOfPar lam (Finset.univ.image fun x => (f x, true)) := by
  obtain ⟨s, rfl⟩ := hodd
  have hT : (Finset.univ.image f).card = 2 * s + 1 := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, hN]
  let c : Fin (2 * s + 1) → ℚ := fun i => (Finset.univ.image f).orderEmbOfFin hT i.rev
  have hc : StrictAnti c := fun i j hij =>
    ((Finset.univ.image f).orderEmbOfFin hT).strictMono (Fin.rev_lt_rev.mpr hij)
  have hmem : ∀ i, ∃ x, f x = c i := fun i => by
    have := (Finset.univ.image f).orderEmbOfFin_mem hT i.rev
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp this
    exact ⟨x, hx⟩
  have hci : ∀ i, ∃ z : ℤ, c i = z := fun i => by
    obtain ⟨x, hx⟩ := hmem i
    rw [← hx]; exact hz x
  choose z hzc using hci
  refine ⟨⟨fun i => z i - s + (i : ℕ), ?_⟩, ?_, c, hc, ?_, ?_⟩
  · rw [Fin.antitone_iff_succ_le]
    intro i
    have h1 := hc (Fin.castSucc_lt_succ (i := i))
    rw [hzc, hzc] at h1
    have h2 : z i.succ < z i.castSucc := by exact_mod_cast h1
    simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    omega
  · rw [Finset.card_image_of_injective _ (fun x y h => hf (Prod.ext_iff.mp h).1), Finset.card_univ, hN]
  · intro i
    obtain ⟨x, hx⟩ := hmem i
    exact ⟨true, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by rw [hx]⟩⟩
  · intro i
    simp only [rhoVec, hzc]
    push_cast
    ring

/- English proof (translation)
Establish `hm : ¬ Odd D.R.m` using `Nat.not_odd_iff_even.mpr D.R.m_even`. Use extensionality with `⟨y, s⟩`. Simplify using `only [TPar.Dpar, TPar.block, hm, if_false, add_zero, Ptw, tparRec, tparHC, Finset.mem_image, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range, Prod.mk.eta, exists_eq_right]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `((⟨i, h⟩ | ⟨i, h⟩) | ⟨i, -, x, ⟨a, ha, rfl⟩, h⟩)`.

Conclude with `⟨.inl i, h⟩`. Use `⟨.inr (.inl i), ?_⟩` and prove the remaining obligations. Rewrite using `[← h]`. Simplify using `[entry]`. Conclude with `⟨.inr (.inr (i, ⟨a, ha⟩)), h⟩`.

Introduce and unpack `⟨i | i | ⟨i, a⟩, h⟩`. Conclude with `.inl (.inl ⟨i, h⟩)`. Use `.inl (.inr ⟨i, ?_⟩)` and prove the remaining obligations. Rewrite using `[← h]`. Simplify using `[entry]`.

Conclude with `.inr ⟨i, i.2, _, ⟨a, a.2, rfl⟩, h⟩`.
-/
lemma dpar_eq (D : D7) (τ : D.what₂.Tau) :
    (Ptw D).Dpar D.R.m τ = Finset.univ.image fun x => (entry (D.hc τ) x, true) := by
  have hm : ¬ Odd D.R.m := Nat.not_odd_iff_even.mpr D.R.m_even
  ext ⟨y, s⟩
  simp only [TPar.Dpar, TPar.block, hm, if_false, add_zero, Ptw, tparRec, tparHC, Finset.mem_image,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range, Prod.mk.eta, exists_eq_right]
  constructor
  · rintro ((⟨i, h⟩ | ⟨i, h⟩) | ⟨i, -, x, ⟨a, ha, rfl⟩, h⟩)
    · exact ⟨.inl i, h⟩
    · refine ⟨.inr (.inl i), ?_⟩
      rw [← h]
      simp [entry]
    · exact ⟨.inr (.inr (i, ⟨a, ha⟩)), h⟩
  · rintro ⟨i | i | ⟨i, a⟩, h⟩
    · exact .inl (.inl ⟨i, h⟩)
    · refine .inl (.inr ⟨i, ?_⟩)
      rw [← h]
      simp [entry]
    · exact .inr ⟨i, i.2, _, ⟨a, a.2, rfl⟩, h⟩

/- English proof (translation)
Introduce `τ`. Establish `h : ∃ lam : DomWeight D.sp.X'.rank, Bridge.IsWtOfPar lam ((Ptw D).Dpar D.R.m τ)`. Rewrite using `[dpar_eq]`. Establish `hk` using `D.R.m_add_three_le_k`. Use `exists_isWtOfPar _ (entry_injective _) (entry_int _) ?_ ?_` and prove the remaining obligations.

Rewrite using `[D.sp.X'_rank]`. Simplify using `only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Ranks.rankX', Ranks.r]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[D.sp.X'_rank]`. Use `Odd.add_even ?_ (D.R.m_even.mul_right _)` and prove the remaining obligations.

Take `⟨a, ha⟩` from `D.R.k_even`. Take `⟨b, hb⟩` from `D.R.m_even`. Conclude with `⟨a + b - 1, by unfold Ranks.r; omega⟩`. Unfold `Bridge.lamRdef`. Rewrite using `[dif_pos h]`.

Conclude with `h.choose_spec`.
-/
theorem lamRForced (D : D7) : Bridge.LamRForced (Ptw D) := by
  intro τ
  have h : ∃ lam : DomWeight D.sp.X'.rank, Bridge.IsWtOfPar lam ((Ptw D).Dpar D.R.m τ) := by
    rw [dpar_eq]
    have hk := D.R.m_add_three_le_k
    refine exists_isWtOfPar _ (entry_injective _) (entry_int _) ?_ ?_
    · rw [D.sp.X'_rank]
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Ranks.rankX', Ranks.r]
      omega
    · rw [D.sp.X'_rank]
      refine Odd.add_even ?_ (D.R.m_even.mul_right _)
      obtain ⟨a, ha⟩ := D.R.k_even
      obtain ⟨b, hb⟩ := D.R.m_even
      exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
  unfold Bridge.lamRdef
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Introduce `j hj1 hjm τ`. Establish `h : ∃ lam : DomWeight (D.sp.V j).rank, Bridge.IsLamPrime (D` using `D) lam j τ := by`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Establish `hj : j - 1 < D.R.m` using `by omega`.

Take `⟨e, he⟩` from `(D.hc τ).e_int ⟨j - 1, hj⟩`. Use `choose v hv using (D.hc τ).v_int`. Use `choose b hb using (D.hc τ).b_int`. Set `W : IndefiniteWeightData.WeightData` to `{ k := D.R.k, m := D.R.m, t := D.R.t, j := j, e := e v := fun n => if h : n - 2 < D.R.k - 1 then v ⟨n - 2, h⟩ else 0 b := fun n => if h : n - 1 < D.R.m then b ⟨n - 1, h⟩ else 0 }`. Establish `hWv : ∀ (n : ℕ) (h : n - 2 < D.R.k - 1), (W.v n : ℚ) = (D.hc τ).v ⟨n - 2, h⟩`.

Introduce `n h`. Simplify using `only [W, dif_pos h, hv]`. Establish `hWb : ∀ (n : ℕ) (h : n - 1 < D.R.m), (W.b n : ℚ) = (D.hc τ).b ⟨n - 1, h⟩`. Introduce `n h`. Simplify using `only [W, dif_pos h, hb]`.

Establish `hWe : (W.e : ℚ) = (D.hc τ).e ⟨j - 1, hj⟩` using `he.symm`. Establish `ht : (0 : ℚ) ≤ D.R.t` using `by positivity`. Establish `hg : W.GapHyp`. Use `⟨?_, fun hlt => ?_⟩` and prove the remaining obligations. Rewrite using `[hWe, hWb W.j hj]`.

Conclude with `(D.hc τ).gap_be _`. Establish `hlt' : j < D.R.m` using `hlt`. Rewrite using `[hWe, hWb (W.j + 1) hlt']`. Use `eb (D.hc τ) (i := ⟨j - 1, hj⟩) (j := ⟨j, hlt'⟩) (by rw [Fin.lt_def]; simp only; omega)` as an intermediate fact. Express the relevant statement in the definitionally equal form `((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨j, hlt'⟩ - _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hH : W.Hyp`. Use `⟨show 1 ≤ D.R.k by omega, hj1, hjm, ?_, D.R.t_odd, ?_, ?_, fun hlt => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `D.R.k_even`. Take `⟨b, hb⟩` from `D.R.m_even`.

Conclude with `⟨a + b - 1, show D.R.k + D.R.m - 1 = _ by omega⟩`. Introduce `i hi1 hir`. Establish `hir' : i < D.R.k + D.R.m - 1` using `hir`. Establish `hWk : W.k = D.R.k` using `rfl`. Rewrite using `[← Int.cast_lt (R := ℚ)]`.

Unfold `IndefiniteWeightData.WeightData.lam`. Rewrite using `[hWk]`. Use `split_ifs with h1 h2 h2`. Rewrite using `[hWv _ (by omega), hWv _ (by omega)]`. Conclude with `v_strictAnti _ (by rw [Fin.lt_def]; simp only; omega)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Int.cast_neg, hWv _ (by omega), hWb _ (by omega)]`. Conclude with `negb_lt_v _ _ _`. Rewrite using `[Int.cast_neg, Int.cast_neg, hWb _ (by omega), hWb _ (by omega), neg_lt_neg_iff]`. Conclude with `b_strictMono _ (by rw [Fin.lt_def]; simp only; omega)`.

Rewrite using `[← Int.cast_lt (R := ℚ)]`. Establish `h1` using `hg.1`. Establish `: (W.t : ℚ) = D.R.t` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← Int.cast_lt (R := ℚ)]`.

Establish `h1` using `hg.2 hlt`. Establish `: (W.t : ℚ) = D.R.t` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨-, -, -, hint, hdom, -⟩` from `GlobalTheory.LowestKType.thetaSide W hH hg`. Establish `hr : (D.sp.V j).rank = W.nV` using `D.sp.V_rank j hj1 hjm`.

Establish `hint' : ∀ i : Fin (D.sp.V j).rank, ∃ z : ℤ, W.lamPrime (i + 1) = z` using `fun i => hint _ (by omega) (by have := i.2; omega)`. Use `choose z hz using hint'`. Establish `hanti : ∀ d i : ℕ, i + d + 1 ≤ W.nV → W.lamPrime (i + d + 1) ≤ W.lamPrime (i + 1)`. Introduce `d i`. Proceed by induction on `d with`.

Consider the case `zero => intro _`. Conclude with `le_rfl`. Consider the case `succ d ih`. Introduce `hd`. Conclude with `(hdom (i + d + 1) (by omega) (by omega)).trans (ih (by omega))`.

Use `⟨⟨z, ?_⟩, ⟨hj1, hj⟩, W, rfl, rfl, rfl, rfl, hWe, fun a => hWv (a + 2) a.2, fun a => hWb (a + 1) a.2, fun i => (hz i).symm⟩` and prove the remaining obligations. Introduce `i i' hii`. Rewrite using `[← Int.cast_le (R := ℚ), ← hz, ← hz]`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le (show (i : ℕ) ≤ i' from hii)`. Use `i'.2` as an intermediate fact.

Rewrite using `[hd]`. Conclude with `hanti d i (by omega)`. Unfold `Bridge.lamLdef`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem lamLForced (D : D7) : Bridge.LamLForced D := by
  intro j hj1 hjm τ
  have h : ∃ lam : DomWeight (D.sp.V j).rank, Bridge.IsLamPrime (D := D) lam j τ := by
    have hk := D.R.m_add_three_le_k
    have hm := D.R.two_le_m
    have hj : j - 1 < D.R.m := by omega
    obtain ⟨e, he⟩ := (D.hc τ).e_int ⟨j - 1, hj⟩
    choose v hv using (D.hc τ).v_int
    choose b hb using (D.hc τ).b_int
    let W : IndefiniteWeightData.WeightData :=
      { k := D.R.k, m := D.R.m, t := D.R.t, j := j, e := e
        v := fun n => if h : n - 2 < D.R.k - 1 then v ⟨n - 2, h⟩ else 0
        b := fun n => if h : n - 1 < D.R.m then b ⟨n - 1, h⟩ else 0 }
    have hWv : ∀ (n : ℕ) (h : n - 2 < D.R.k - 1), (W.v n : ℚ) = (D.hc τ).v ⟨n - 2, h⟩ := by
      intro n h
      simp only [W, dif_pos h, hv]
    have hWb : ∀ (n : ℕ) (h : n - 1 < D.R.m), (W.b n : ℚ) = (D.hc τ).b ⟨n - 1, h⟩ := by
      intro n h
      simp only [W, dif_pos h, hb]
    have hWe : (W.e : ℚ) = (D.hc τ).e ⟨j - 1, hj⟩ := he.symm
    have ht : (0 : ℚ) ≤ D.R.t := by positivity
    have hg : W.GapHyp := by
      refine ⟨?_, fun hlt => ?_⟩
      · rw [hWe, hWb W.j hj]
        exact (D.hc τ).gap_be _
      · have hlt' : j < D.R.m := hlt
        rw [hWe, hWb (W.j + 1) hlt']
        have := eb (D.hc τ) (i := ⟨j - 1, hj⟩) (j := ⟨j, hlt'⟩) (by rw [Fin.lt_def]; simp only; omega)
        change ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨j, hlt'⟩ - _
        linarith
    have hH : W.Hyp := by
      refine ⟨show 1 ≤ D.R.k by omega, hj1, hjm, ?_, D.R.t_odd, ?_, ?_, fun hlt => ?_⟩
      · obtain ⟨a, ha⟩ := D.R.k_even
        obtain ⟨b, hb⟩ := D.R.m_even
        exact ⟨a + b - 1, show D.R.k + D.R.m - 1 = _ by omega⟩
      · intro i hi1 hir
        have hir' : i < D.R.k + D.R.m - 1 := hir
        have hWk : W.k = D.R.k := rfl
        rw [← Int.cast_lt (R := ℚ)]
        unfold IndefiniteWeightData.WeightData.lam
        rw [hWk]
        split_ifs with h1 h2 h2
        · rw [hWv _ (by omega), hWv _ (by omega)]
          exact v_strictAnti _ (by rw [Fin.lt_def]; simp only; omega)
        · omega
        · rw [Int.cast_neg, hWv _ (by omega), hWb _ (by omega)]
          exact negb_lt_v _ _ _
        · rw [Int.cast_neg, Int.cast_neg, hWb _ (by omega), hWb _ (by omega), neg_lt_neg_iff]
          exact b_strictMono _ (by rw [Fin.lt_def]; simp only; omega)
      · rw [← Int.cast_lt (R := ℚ)]
        have h1 := hg.1
        have : (W.t : ℚ) = D.R.t := rfl
        linarith
      · rw [← Int.cast_lt (R := ℚ)]
        have h1 := hg.2 hlt
        have : (W.t : ℚ) = D.R.t := rfl
        linarith
    obtain ⟨-, -, -, hint, hdom, -⟩ := GlobalTheory.LowestKType.thetaSide W hH hg
    have hr : (D.sp.V j).rank = W.nV := D.sp.V_rank j hj1 hjm
    have hint' : ∀ i : Fin (D.sp.V j).rank, ∃ z : ℤ, W.lamPrime (i + 1) = z := fun i =>
      hint _ (by omega) (by have := i.2; omega)
    choose z hz using hint'
    have hanti : ∀ d i : ℕ, i + d + 1 ≤ W.nV → W.lamPrime (i + d + 1) ≤ W.lamPrime (i + 1) := by
      intro d i
      induction d with
      | zero => intro _; exact le_rfl
      | succ d ih =>
        intro hd
        exact (hdom (i + d + 1) (by omega) (by omega)).trans (ih (by omega))
    refine ⟨⟨z, ?_⟩, ⟨hj1, hj⟩, W, rfl, rfl, rfl, rfl, hWe, fun a => hWv (a + 2) a.2,
      fun a => hWb (a + 1) a.2, fun i => (hz i).symm⟩
    intro i i' hii
    rw [← Int.cast_le (R := ℚ), ← hz, ← hz]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show (i : ℕ) ≤ i' from hii)
    have := i'.2
    rw [hd]
    exact hanti d i (by omega)
  unfold Bridge.lamLdef
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Introduce `D` and use `⟨lamRForced D, lamLForced D⟩`.
-/
theorem lam_forced : ∀ D : D7, Bridge.LamRForced (Ptw D) ∧ Bridge.LamLForced D :=
  fun D => ⟨lamRForced D, lamLForced D⟩

end GlobalTheory.ForcedWeights
