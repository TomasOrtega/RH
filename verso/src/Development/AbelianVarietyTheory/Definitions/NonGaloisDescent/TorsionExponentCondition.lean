import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.HubX.Check

variable {D : D7}

/- English proof (translation)
The claim follows from `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`.
-/
theorem one_le_Lg (L : SizeData₂ D) : 1 ≤ TwistedPlaces.large₂ L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

/- English proof (translation)
Establish `h1` using `one_le_Lg L`. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 2 ^ Nat.log l k ≤ k` using `(Nat.pow_le_pow_left hl _).trans (Nat.pow_log_le_self l hk0.ne')`.

Establish `h3 : (2 : ℝ) ^ Nat.log l k ≤ 8 * L.sc.b` using `le_trans (by exact_mod_cast h2) hk`. Establish `h4` using `Real.log_le_log (by positivity) h3`. Establish `hb : Real.log (8 * L.sc.b) = 3 * Real.log 2 + TwistedPlaces.large₂ L`. Rewrite using `[Scale.b, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]`. Evaluate the numerical expressions.

Rewrite `h4` using `[Real.log_pow, hb]`. Establish `h5` using `Real.log_two_gt_d9`. Establish `h6 : (0 : ℝ) ≤ Nat.log l k` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_le_Lg (L : SizeData₂ D) (l k : ℕ) (hl : 2 ≤ l) (hk : (k : ℝ) ≤ 8 * L.sc.b) :
    (Nat.log l k : ℝ) ≤ 5 * TwistedPlaces.large₂ L := by
  have h1 := one_le_Lg L
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp; linarith
  have h2 : 2 ^ Nat.log l k ≤ k :=
    (Nat.pow_le_pow_left hl _).trans (Nat.pow_log_le_self l hk0.ne')
  have h3 : (2 : ℝ) ^ Nat.log l k ≤ 8 * L.sc.b := le_trans (by exact_mod_cast h2) hk
  have h4 := Real.log_le_log (by positivity) h3
  have hb : Real.log (8 * L.sc.b) = 3 * Real.log 2 + TwistedPlaces.large₂ L := by
    rw [Scale.b, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_pow, hb] at h4
  have h5 := Real.log_two_gt_d9
  have h6 : (0 : ℝ) ≤ Nat.log l k := by positivity
  nlinarith

/- English proof (translation)
The claim follows from `Real.one_le_exp (le_trans zero_le_one (one_le_Lg L))`.
-/
theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (le_trans zero_le_one (one_le_Lg L))

/- English proof (translation)
Establish `h` using `D.R.three_m_lt_t`. Use `⟨by exact_mod_cast (by omega : 1 ≤ D.R.t), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(D.R.ord_pos : 0 < D.R.n)` after adjusting the coercions. Establish `: 1 ≤ D.R.nV` using `by unfold Ranks.nV; omega`. Conclude with `this` after adjusting the coercions.
-/
theorem sizes (D : D7) : (1 : ℝ) ≤ D.R.t ∧ (1 : ℝ) ≤ D.R.n ∧ (1 : ℝ) ≤ D.R.nV := by
  have h := D.R.three_m_lt_t
  refine ⟨by exact_mod_cast (by omega : 1 ≤ D.R.t), ?_, ?_⟩
  · exact_mod_cast (D.R.ord_pos : 0 < D.R.n)
  · have : 1 ≤ D.R.nV := by unfold Ranks.nV; omega
    exact_mod_cast this

variable {L : SizeData₂ D} {HW : HWOf D.loc} {R : KillingConditions.RowK} {X : KillingConditions.HubData D}

/- English proof (translation)
Introduce `i _ _ _`. Rewrite using `[h.cB]`. Establish `hb` using `one_le_b L`. Establish `hf : ((⌊2 * L.sc.b⌋₊ : ℕ) : ℝ) ≤ 2 * L.sc.b` using `Nat.floor_le (by linarith)`. Establish `hlog` using `log_le_Lg L (D.nd.l i) (2 * ⌊2 * L.sc.b⌋₊) (D.nd.lPrime i).out.two_le (by push_cast; linarith)`.

Take `⟨ht, hn, hv⟩` from `sizes D`. Establish `hL` using `one_le_Lg L`. Unfold `cBof GlobalTheory.HubLoc.cBnum`. Use `push_cast`. Generalize the expression as in `(Nat.log (D.nd.l i) (2 * ⌊2 * L.sc.b⌋₊) : ℝ) = a at *`.

Generalize the expression as in `(D.R.t : ℝ) = t at *`. Generalize the expression as in `TwistedPlaces.large₂ L = y at *`. Establish `hN : 1 ≤ (D.R.n : ℝ) * D.R.nV` using `one_le_mul_of_one_le_of_one_le hn hv`. Establish `e : (80 : ℝ) * t * D.R.n * D.R.nV * y = 80 * (t * (D.R.n * D.R.nV) * y)` using `by ring`. Establish `e2 : (4 : ℝ) * D.R.n * D.R.nV = 4 * (D.R.n * D.R.nV)` using `by ring`.

Rewrite using `[e, e2]`. Generalize the expression as in `(D.R.n : ℝ) * D.R.nV = N at *`. Establish `p1 : t * N * (4 + 2 * a) ≤ t * N * (14 * y)` using `by gcongr; linarith`. Establish `p2 : 1 ≤ t * N` using `one_le_mul_of_one_le_of_one_le ht hN`. Establish `p3 : y ≤ t * N * y` using `by nlinarith`.

Establish `p4 : t ≤ t * N` using `by nlinarith`. Establish `p5 : t * N ≤ t * N * y` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem condCB (h : Canon L HW R X) : CondCB L X 80 := by
  intro i _ _ _
  rw [h.cB]
  have hb := one_le_b L
  have hf : ((⌊2 * L.sc.b⌋₊ : ℕ) : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  have hlog := log_le_Lg L (D.nd.l i) (2 * ⌊2 * L.sc.b⌋₊) (D.nd.lPrime i).out.two_le (by push_cast; linarith)
  obtain ⟨ht, hn, hv⟩ := sizes D
  have hL := one_le_Lg L
  unfold cBof GlobalTheory.HubLoc.cBnum
  push_cast
  generalize (Nat.log (D.nd.l i) (2 * ⌊2 * L.sc.b⌋₊) : ℝ) = a at *
  generalize (D.R.t : ℝ) = t at *
  generalize TwistedPlaces.large₂ L = y at *
  have hN : 1 ≤ (D.R.n : ℝ) * D.R.nV := one_le_mul_of_one_le_of_one_le hn hv
  have e : (80 : ℝ) * t * D.R.n * D.R.nV * y = 80 * (t * (D.R.n * D.R.nV) * y) := by ring
  have e2 : (4 : ℝ) * D.R.n * D.R.nV = 4 * (D.R.n * D.R.nV) := by ring
  rw [e, e2]
  generalize (D.R.n : ℝ) * D.R.nV = N at *
  have p1 : t * N * (4 + 2 * a) ≤ t * N * (14 * y) := by gcongr; linarith
  have p2 : 1 ≤ t * N := one_le_mul_of_one_le_of_one_le ht hN
  have p3 : y ≤ t * N * y := by nlinarith
  have p4 : t ≤ t * N := by nlinarith
  have p5 : t * N ≤ t * N * y := by nlinarith
  nlinarith

/- English proof (translation)
Introduce `i _ _ _ _ u _`. Rewrite using `[h.c0]`. Establish `hb` using `one_le_b L`. Establish `hf : ((⌊2 * L.sc.b⌋₊ : ℕ) : ℝ) ≤ 2 * L.sc.b` using `Nat.floor_le (by linarith)`. Establish `hlog` using `log_le_Lg L (D.nd.l i) (2 * hOf L) (D.nd.lPrime i).out.two_le (by unfold hOf; push_cast; linarith)`.

Take `⟨-, hn, hv⟩` from `sizes D`. Establish `hL` using `one_le_Lg L`. Unfold `c0of`. Use `push_cast`. Generalize the expression as in `(Nat.log (D.nd.l i) (2 * hOf L) : ℝ) = a at *`.

Generalize the expression as in `TwistedPlaces.large₂ L = y at *`. Establish `hN : 1 ≤ (D.R.n : ℝ) * D.R.nV` using `one_le_mul_of_one_le_of_one_le hn hv`. Establish `e : (80 : ℝ) * D.R.n * D.R.nV * y = 80 * ((D.R.n * D.R.nV) * y)` using `by ring`. Establish `e2 : (4 : ℝ) * D.R.n * D.R.nV = 4 * (D.R.n * D.R.nV)` using `by ring`. Rewrite using `[e, e2]`.

Generalize the expression as in `(D.R.n : ℝ) * D.R.nV = N at *`. Establish `p1 : N * (4 + 2 * a) ≤ N * (14 * y)` using `by gcongr; linarith`. Establish `p3 : y ≤ N * y` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem torsion_exponent_condition (h : Canon L HW R X) : KillingConditions.ConstantColumnBound L X 80 := by
  intro i _ _ _ _ u _
  rw [h.c0]
  have hb := one_le_b L
  have hf : ((⌊2 * L.sc.b⌋₊ : ℕ) : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  have hlog := log_le_Lg L (D.nd.l i) (2 * hOf L) (D.nd.lPrime i).out.two_le (by unfold hOf; push_cast; linarith)
  obtain ⟨-, hn, hv⟩ := sizes D
  have hL := one_le_Lg L
  unfold c0of
  push_cast
  generalize (Nat.log (D.nd.l i) (2 * hOf L) : ℝ) = a at *
  generalize TwistedPlaces.large₂ L = y at *
  have hN : 1 ≤ (D.R.n : ℝ) * D.R.nV := one_le_mul_of_one_le_of_one_le hn hv
  have e : (80 : ℝ) * D.R.n * D.R.nV * y = 80 * ((D.R.n * D.R.nV) * y) := by ring
  have e2 : (4 : ℝ) * D.R.n * D.R.nV = 4 * (D.R.n * D.R.nV) := by ring
  rw [e, e2]
  generalize (D.R.n : ℝ) * D.R.nV = N at *
  have p1 : N * (4 + 2 * a) ≤ N * (14 * y) := by gcongr; linarith
  have p3 : y ≤ N * y := by nlinarith
  nlinarith

/- English proof (translation)
Rewrite using `[h.eta]`. Use `L.etaSz_pos` as an intermediate fact. Conclude with `⟨(Nat.floor_le this.le).trans (by linarith), (Nat.lt_floor_add_one _).le⟩`.
-/
theorem eta_le (h : Canon L HW R X) : (X.eta : ℝ) ≤ 2 * L.etaSz ∧ L.etaSz ≤ (X.eta : ℝ) + 1 := by
  rw [h.eta]
  have := L.etaSz_pos
  exact ⟨(Nat.floor_le this.le).trans (by linarith), (Nat.lt_floor_add_one _).le⟩

/- English proof (translation)
Introduce `h2`. Unfold `TwistedPlaces.SplitK at h1`. Unfold `TwistedPlaces.InertK at h2`. Rewrite `h2` using `[h1]`. Apply the tactic sequence `rcases h2 with h2 | h2 <;> cases h2`.
-/
theorem not_inert {l : ℕ} (h1 : TwistedPlaces.SplitK D l) : ¬ TwistedPlaces.InertK D l := by
  intro h2
  unfold TwistedPlaces.SplitK at h1
  unfold TwistedPlaces.InertK at h2
  rw [h1] at h2
  rcases h2 with h2 | h2 <;> cases h2

/- English proof (translation)
Establish `hp` using `(D.nd.lPrime i).out`. Establish `h5 : 5 ≤ D.nd.l i`. Establish `h2` using `hp.two_le`. Establish `h3 : D.nd.l i ≠ 3` using `fun e => hr.1 (Or.inr e)`. Establish `h2' : D.nd.l i ≠ 2` using `fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))`.

Establish `h4 : D.nd.l i ≠ 4` using `fun e => by rw [e] at hp; norm_num at hp`. Use linear arithmetic over natural numbers and integers. Establish `hsp : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i)`. Use `⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩` and prove the remaining obligations. Rewrite using `[e]`.

Apply the tactic sequence `fin_cases k <;> simp [TwistedPlaces.gset]`. Establish `he : epJ D = hJ.choose` using `epJ_eq hJ`. Establish `hc : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) ∧ ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc (epJ D)` using `⟨hsp, by rw [he]; exact hex⟩`. Rewrite using `[h.dc i (not_inert hs), dcOf, dif_pos hc, ← he]`. Conclude with `hc.2.choose_spec`.
-/
theorem decl (h : Canon L HW R X) (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc) (hg : D.nd.l i ∉ TwistedPlaces.gset D)
    (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i))
    (hex : ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc hJ.choose) : EmbeddingTypes.hypDecl i (X.dc i) hJ.choose := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  have hsp : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
    refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
    rw [e]
    fin_cases k <;> simp [TwistedPlaces.gset]
  have he : epJ D = hJ.choose := epJ_eq hJ
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) ∧ ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc (epJ D) :=
    ⟨hsp, by rw [he]; exact hex⟩
  rw [h.dc i (not_inert hs), dcOf, dif_pos hc, ← he]
  exact hc.2.choose_spec

/- English proof (translation)
Distinguish the cases in `hi : TwistedPlaces.InertK D (D.nd.l i)`. Conclude with `h.data.col i hi`. Rewrite using `[h.dc i hi, dcOf, dif_neg (fun c => hn c.1)]`. Both sides reduce to the same expression.
-/
theorem col_empty (h : Canon L HW R X) (i : D.nd.Loc)
    (hn : ¬ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i)) : (X.dc i).col = ∅ := by
  by_cases hi : TwistedPlaces.InertK D (D.nd.l i)
  · exact h.data.col i hi
  · rw [h.dc i hi, dcOf, dif_neg (fun c => hn c.1)]
    rfl

/- English proof (translation)
Establish `hl` using `(D.nd.lPrime i).out`. Unfold `c0of`. Establish `hN1 : 1 ≤ 4 * D.R.n * D.R.nV`. Take `⟨-, hn, hv⟩` from `sizes D`. Establish `a : 1 ≤ D.R.n` using `by exact_mod_cast hn`.

Establish `b : 1 ≤ D.R.nV` using `by exact_mod_cast hv`. Conclude with `Nat.mul_pos (by omega) b`. Generalize the expression as in `4 * D.R.n * D.R.nV = N at *`. Generalize the expression as in `hOf L = h at *`. Use `set l := D.nd.l i`.

Use `set lam := Nat.log l (2 * h) with hlam`. Establish `hn0 : LocalSituation.n0 l (h + h) ≤ lam + 1`. Use `Nat.sInf_le ?_` and prove the remaining obligations. Establish `h1` using `Nat.lt_pow_succ_log_self hl.one_lt (2 * h)`. Establish `h2 : 1 ≤ l - 1` using `by have := hl.two_le; omega`.

Use `show h + h ≤ l ^ (lam + 1) * (l - 1)`. Combine the equalities or inequalities in the displayed calculation. Establish `hm : LocalSituation.mN l 1 (h + h) ≤ 4 + lam` using `by unfold LocalSituation.mN; omega`. Use `set m := LocalSituation.mN l 1 (h + h)`. Establish `hr : LocalSituation.rI l m U' 0 ≤ N * (4 + 2 * lam)`.

Establish `hfin : ({u | u ∈ U' ∧ u ≠ 0} : Set ℤ).Finite` using `U.finite_toSet.subset fun u hu => hU hu.1`. Establish `e1 : LocalSituation.rI l m U' 0 = ∑ u ∈ hfin.toFinset, (m + LocalSituation.vZ l (u - 0))`. Rewrite using `[← finsum_mem_eq_finite_toFinset_sum _ hfin]`. Unfold `LocalSituation.rI`. Use `finsum_congr fun u => ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases h1 : u ∈ U' <;> by_cases h2 : u = 0 <;> simp [h1, h2]`. Rewrite using `[e1]`. Establish `hc : hfin.toFinset.card ≤ N` using `(Finset.card_le_card fun u hu => hU (hfin.mem_toFinset.1 hu).1).trans hN`. Use `(Finset.sum_le_card_nsmul _ _ (4 + 2 * lam) fun u hu => ?_).trans (Nat.mul_le_mul_right _ hc)` and prove the remaining obligations. Establish `hu'` using `hfin.mem_toFinset.1 hu`.

Establish `h1` using `hb u (hU hu'.1)`. Establish `h2 : LocalSituation.vZ l (u - 0) ≤ lam`. Unfold `LocalSituation.vZ padicValInt`. Use `(padicValNat_le_nat_log _).trans (Nat.log_mono_right ?_)` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Establish `h1 : 1 ≤ N * (4 + 2 * lam)` using `Nat.mul_pos hN1 (by omega)`. Unfold `LocalSituation.cLL`. Rewrite using `[show Finset.Ico (0 : ℤ) 1 = {0} from rfl, Finset.sum_singleton]`. Use linear arithmetic over natural numbers and integers.
-/
theorem cLL_le (L : SizeData₂ D) (i : D.nd.Loc) (u : HeightOneSpectrum (𝓞 D.host.E)) (U : Finset ℤ) (U' : Set ℤ)
    (hU : U' ⊆ U) (hN : U.card ≤ 4 * D.R.n * D.R.nV) (hb : ∀ a ∈ U, -(hOf L : ℤ) ≤ a ∧ a ≤ hOf L) :
    LocalSituation.cLL (D.nd.l i) (LocalSituation.mN (D.nd.l i) 1 (hOf L + hOf L)) (LocalSituation.mN (D.nd.l i) 1 (hOf L + hOf L) - 1) U' 0 1 ≤
      c0of L i u := by
  have hl := (D.nd.lPrime i).out
  unfold c0of
  have hN1 : 1 ≤ 4 * D.R.n * D.R.nV := by
    obtain ⟨-, hn, hv⟩ := sizes D
    have a : 1 ≤ D.R.n := by exact_mod_cast hn
    have b : 1 ≤ D.R.nV := by exact_mod_cast hv
    exact Nat.mul_pos (by omega) b
  generalize 4 * D.R.n * D.R.nV = N at *
  generalize hOf L = h at *
  set l := D.nd.l i
  set lam := Nat.log l (2 * h) with hlam
  have hn0 : LocalSituation.n0 l (h + h) ≤ lam + 1 := by
    refine Nat.sInf_le ?_
    have h1 := Nat.lt_pow_succ_log_self hl.one_lt (2 * h)
    have h2 : 1 ≤ l - 1 := by have := hl.two_le; omega
    show h + h ≤ l ^ (lam + 1) * (l - 1)
    calc h + h = 2 * h := by ring
      _ ≤ l ^ (lam + 1) := h1.le
      _ ≤ _ := Nat.le_mul_of_pos_right _ h2
  have hm : LocalSituation.mN l 1 (h + h) ≤ 4 + lam := by unfold LocalSituation.mN; omega
  set m := LocalSituation.mN l 1 (h + h)
  have hr : LocalSituation.rI l m U' 0 ≤ N * (4 + 2 * lam) := by
    have hfin : ({u | u ∈ U' ∧ u ≠ 0} : Set ℤ).Finite := U.finite_toSet.subset fun u hu => hU hu.1
    have e1 : LocalSituation.rI l m U' 0 = ∑ u ∈ hfin.toFinset, (m + LocalSituation.vZ l (u - 0)) := by
      rw [← finsum_mem_eq_finite_toFinset_sum _ hfin]
      unfold LocalSituation.rI
      refine finsum_congr fun u => ?_
      by_cases h1 : u ∈ U' <;> by_cases h2 : u = 0 <;> simp [h1, h2]
    rw [e1]
    have hc : hfin.toFinset.card ≤ N :=
      (Finset.card_le_card fun u hu => hU (hfin.mem_toFinset.1 hu).1).trans hN
    refine (Finset.sum_le_card_nsmul _ _ (4 + 2 * lam) fun u hu => ?_).trans (Nat.mul_le_mul_right _ hc)
    have hu' := hfin.mem_toFinset.1 hu
    have h1 := hb u (hU hu'.1)
    have h2 : LocalSituation.vZ l (u - 0) ≤ lam := by
      unfold LocalSituation.vZ padicValInt
      refine (padicValNat_le_nat_log _).trans (Nat.log_mono_right ?_)
      omega
    omega
  have h1 : 1 ≤ N * (4 + 2 * lam) := Nat.mul_pos hN1 (by omega)
  unfold LocalSituation.cLL
  rw [show Finset.Ico (0 : ℤ) 1 = {0} from rfl, Finset.sum_singleton]
  omega

/- English proof (translation)
Take `⟨k1, -, -, k4⟩` from `hJ`. Establish `k` using `abs_le.1 (k1 j h1 h2 ρ up _ ha)`. Establish `ht : (3 : ℝ) ≤ D.R.t`. Use `D.R.three_m_lt_t` as an intermediate fact. Use `D.R.two_le_m` as an intermediate fact.

Conclude with `(by omega : 3 ≤ D.R.t)` after adjusting the coercions. Establish `hb` using `one_le_b L`. Establish `hS` using `L.Sc_pos`. Establish `he` using `L.etaSz_pos`. Unfold `AdmissibleParameterJ.hJ at k4`.

Unfold `AdmissibleParameterJ.c0 at k`. Move the coercions through the operations in `at k`. Establish `hc : ((⌊2 * L.sc.b⌋₊ : ℕ) : ℤ) = ⌊2 * L.sc.b⌋` using `Int.natCast_floor_eq_floor (by linarith)`. Use `⟨⟨?_, ?_⟩, Nat.le_floor (by linarith)⟩` and prove the remaining obligations. Rewrite using `[hc, neg_le, Int.le_floor]`.

Use `push_cast`. Combine the linear relations using `[k.1]`. Rewrite using `[hc, Int.le_floor]`. Use `push_cast`. Combine the linear relations using `[k.2]`.
-/
theorem window (L : SizeData₂ D) (hJ : AdmissibleParameterJ.JumpAbsoluteBound L) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ρ : D.what₂.Tau) (up : Bool)
    (a : ℤ) (ha : (a : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ) :
    (-(⌊2 * L.sc.b⌋₊ : ℤ) ≤ a ∧ a + 1 ≤ (⌊2 * L.sc.b⌋₊ : ℤ)) ∧ D.R.t ≤ ⌊2 * L.sc.b⌋₊ := by
  obtain ⟨k1, -, -, k4⟩ := hJ
  have k := abs_le.1 (k1 j h1 h2 ρ up _ ha)
  have ht : (3 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    have := D.R.two_le_m
    exact_mod_cast (by omega : 3 ≤ D.R.t)
  have hb := one_le_b L
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  unfold AdmissibleParameterJ.hJ at k4
  unfold AdmissibleParameterJ.c0 at k
  push_cast at k
  have hc : ((⌊2 * L.sc.b⌋₊ : ℕ) : ℤ) = ⌊2 * L.sc.b⌋ := Int.natCast_floor_eq_floor (by linarith)
  refine ⟨⟨?_, ?_⟩, Nat.le_floor (by linarith)⟩
  · rw [hc, neg_le, Int.le_floor]; push_cast; linarith [k.1]
  · rw [hc, Int.le_floor]; push_cast; linarith [k.2]

/- English proof (translation)
Take `⟨r, ρ, h⟩` from `GlobalTheory.PtCore.PtFam.exists_pair hC hr`. Conclude with `⟨_, canon_ourX L HW R r ρ (fun _ _ => 0) exc I h, rfl, rfl⟩`.
-/
theorem exists_canon (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (I : TwIn D) (exc : Finset ℕ)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) (hr : ∀ i, ∃ r, GoodR D.nd i r) :
    ∃ X, Canon L HW R X ∧ X.I = I ∧ X.exc = exc := by
  obtain ⟨r, ρ, h⟩ := GlobalTheory.PtCore.PtFam.exists_pair hC hr
  exact ⟨_, canon_ourX L HW R r ρ (fun _ _ => 0) exc I h, rfl, rfl⟩

/- English proof (translation)
Take `⟨P, -, hP⟩` from `h2 i r hr w hw hg x`. Rewrite using `[hP, D.naut.inePol_tw _ _ σ hI]`. Conclude with `h1 i w hw hg P σ hσ`.
-/
theorem wild_charpoly (h1 : DepthZeroG D) (h2 : LgcG D) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) (w) (hw : w ∈ D.nd.S i)
    (hg : ∃ k, w ∈ placesOver D.host.E (D.host.g k)) (x : D.nd.X i) (σ : GE D.nd)
    (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 w)) (hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ = (Polynomial.X - 1) ^ D.R.nV := by
  obtain ⟨P, -, hP⟩ := h2 i r hr w hw hg x
  rw [hP, D.naut.inePol_tw _ _ σ hI]
  exact h1 i w hw hg P σ hσ

end GlobalTheory.HubX.Check

end
