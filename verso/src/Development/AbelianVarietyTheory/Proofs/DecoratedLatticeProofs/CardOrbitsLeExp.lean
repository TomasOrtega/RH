import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminingLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogClassNumberAtLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTenth
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.ChainClassNumbersS

/- English proof (translation)
Establish `hrdeq` using `hH.rd_eq`. Take `⟨-, -, -, -, -, -, hX, -, -, hP, -, -, hg, -⟩` from `hH`. Take `⟨⟨s1, -⟩, s2, -, s4, -⟩` from `hS`. Take `⟨hfin, hcount⟩` from `GlobalTheory.DecoClassCount.card_classes_le X hX.ok n ST SG`. Establish `hle` using `GlobalTheory.ChainClassNumbers.card_orbits_le_principal p hp h`.

Establish `hk : 5 ≤ N.R.k` using `by have := N.R.m_add_three_le_k; have := N.R.two_le_m; omega`. Establish `hf : X.f = N.R.f`. Establish `h1 : X.f = Nat.card X.Tau` using `Nat.card_eq_fintype_card.symm`. Rewrite using `[h1, ← Nat.card_congr pl, Nat.card_prod, Nat.card_eq_fintype_card (α := N.R.A), N.R.card_A]`. Simplify using `[Ranks.f, Ranks.n]`.

Establish `hE : Module.finrank ℚ X.E = 2 * N.R.f`. Establish `h1` using `Module.finrank_mul_finrank ℚ X.F X.E`. Rewrite `h1` using `[hX.ok.rankE, ← hX.ok.card_Tau]`. Rewrite using `[← hf, mul_comm]`. Conclude with `h1.symm`.

Establish `hf1 : 1 ≤ N.R.f` using `hf ▸ hX.ok.f_pos`. Establish `hfib` using `GlobalTheory.ColumnClassLog.fibre_bound_le hP u n hn SG hSG`. Rewrite `hfib` using `[hf, hg 0, hg 1]`. Establish `hsub : ∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n ≤ ∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal ^ n`. Use `Finset.prod_le_prod_of_subset_of_one_le' hST fun P hP' _ => ?_` and prove the remaining obligations.

Rewrite using `[hP.vT_norm u P hP']`. Conclude with `Nat.one_le_pow _ _ (hP.T_prime u).pos`. Establish `hfib'` using `(Nat.mul_le_mul_right _ hsub).trans hfib`. Establish `hrd : |(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) = N.rd`. Establish `e : X.E ≃ₐ[ℚ] D.host.E` using `s.iE.toRatAlgEquiv`.

Establish `h1 : D.host.rdE = N.rd` using `hrdeq.symm`. Rewrite using `[discr_eq_discr_of_algEquiv X.E e, e.toLinearEquiv.finrank_eq]`. Conclude with `h1`. Establish `hrd0 : 0 < N.rd`. Rewrite using `[← hrd]`.

Conclude with `Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero _)) _`. Establish `hL : 1 ≤ N.sc.L` using `Real.one_le_rpow N.sc.one_lt_alt.le N.sc.eps_pos.le`. Establish `hb : 1 ≤ Real.exp N.sc.L` using `Real.one_le_exp (by linarith)`. Establish `hg0 : Real.exp N.sc.L ≤ N.g 0`. Use `le_trans ?_ (s2 0).1` and prove the remaining obligations.

Establish `hk' : (1 : ℝ) ≤ N.R.k` using `by exact_mod_cast (by omega : 1 ≤ N.R.k)`. Establish `h1 : Real.exp N.sc.L ≤ (N.R.k : ℝ) * Real.exp N.sc.L` using `by nlinarith`. Conclude with `h1.trans (le_self_pow₀ (hb.trans h1) (by norm_num))`. Establish `hlog` using `GlobalTheory.ColumnClassLog.log_le_of_count (Nat.card (MulAction.orbitRel.Quotient G' D')) N.R.f n N.Nm (N.g 0) (N.g 1) (Pr.T u) N.rd N.sc.L hf1 hn hnN (hP.T_prime u).pos hrd0 hL s1 s4 hg0 (N.g_prime 1).pos (by`. Use `((Nat.cast_le.2 hle).trans hcount).trans ?_` and prove the remaining obligations.

Rewrite using `[hrd, hE, mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations. Rewrite using `[pow_two n]`. Conclude with `hfib')` after adjusting the coercions. Use `(Real.le_exp_log _).trans (Real.exp_le_exp.2 (hlog.trans ?_))` and prove the remaining obligations.

Establish `hG : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u)`. Establish `: 1 ≤ N.g 0 * N.g 1 * Pr.T u` using `Nat.mul_pos (Nat.mul_pos (N.g_prime 0).pos (N.g_prime 1).pos) (hP.T_prime u).pos`. Conclude with `Real.log_nonneg (by exact_mod_cast this)`. Establish `hm : (1 : ℝ) ≤ (N.R.m : ℝ) ^ 2`. Establish `: (1 : ℝ) ≤ N.R.m` using `by exact_mod_cast (by have := N.R.two_le_m; omega : 1 ≤ N.R.m)`.

Conclude with `one_le_pow₀ this`. Unfold `errUnit`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_orbits_le_exp {D : D7} {N : NumDatum} {X : Fields} {s : Seam D X} {Pr : Primes X} (hH : HostTie N s Pr)
    (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) {δ : Code N} {CY : ℝ} (hS : SizeRowsS CY N δ) {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N.Nm)
    {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (hST : ST ⊆ Pr.vT u) (hSG : SG = Pr.vGs)
    {G' D' : Type} [Group G'] [MulAction G' D'] (p : D' → DecoSet X.E n ST SG) (hp : Function.Injective p)
    (h : ∀ (g : UF X.E n) (x : D'), ∃ g' : G', p (g' • x) = (g, (1 : GLG X.E n SG)) • p x) :
    (Nat.card (MulAction.orbitRel.Quotient G' D') : ℝ) ≤ Real.exp (55 * errUnit N (Pr.T u)) := by
  have hrdeq := hH.rd_eq
  obtain ⟨-, -, -, -, -, -, hX, -, -, hP, -, -, hg, -⟩ := hH
  obtain ⟨⟨s1, -⟩, s2, -, s4, -⟩ := hS
  obtain ⟨hfin, hcount⟩ := GlobalTheory.DecoClassCount.card_classes_le X hX.ok n ST SG
  have hle := GlobalTheory.ChainClassNumbers.card_orbits_le_principal p hp h
  have hk : 5 ≤ N.R.k := by have := N.R.m_add_three_le_k; have := N.R.two_le_m; omega
  have hf : X.f = N.R.f := by
    have h1 : X.f = Nat.card X.Tau := Nat.card_eq_fintype_card.symm
    rw [h1, ← Nat.card_congr pl, Nat.card_prod, Nat.card_eq_fintype_card (α := N.R.A), N.R.card_A]
    simp [Ranks.f, Ranks.n]
  have hE : Module.finrank ℚ X.E = 2 * N.R.f := by
    have h1 := Module.finrank_mul_finrank ℚ X.F X.E
    rw [hX.ok.rankE, ← hX.ok.card_Tau] at h1
    rw [← hf, mul_comm]
    exact h1.symm
  have hf1 : 1 ≤ N.R.f := hf ▸ hX.ok.f_pos
  have hfib := GlobalTheory.ColumnClassLog.fibre_bound_le hP u n hn SG hSG
  rw [hf, hg 0, hg 1] at hfib
  have hsub : ∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n ≤ ∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal ^ n := by
    refine Finset.prod_le_prod_of_subset_of_one_le' hST fun P hP' _ => ?_
    rw [hP.vT_norm u P hP']
    exact Nat.one_le_pow _ _ (hP.T_prime u).pos
  have hfib' := (Nat.mul_le_mul_right _ hsub).trans hfib
  have hrd : |(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) = N.rd := by
    have e : X.E ≃ₐ[ℚ] D.host.E := s.iE.toRatAlgEquiv
    have h1 : D.host.rdE = N.rd := hrdeq.symm
    rw [discr_eq_discr_of_algEquiv X.E e, e.toLinearEquiv.finrank_eq]
    exact h1
  have hrd0 : 0 < N.rd := by
    rw [← hrd]
    exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero _)) _
  have hL : 1 ≤ N.sc.L := Real.one_le_rpow N.sc.one_lt_alt.le N.sc.eps_pos.le
  have hb : 1 ≤ Real.exp N.sc.L := Real.one_le_exp (by linarith)
  have hg0 : Real.exp N.sc.L ≤ N.g 0 := by
    refine le_trans ?_ (s2 0).1
    have hk' : (1 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 1 ≤ N.R.k)
    have h1 : Real.exp N.sc.L ≤ (N.R.k : ℝ) * Real.exp N.sc.L := by nlinarith
    exact h1.trans (le_self_pow₀ (hb.trans h1) (by norm_num))
  have hlog := GlobalTheory.ColumnClassLog.log_le_of_count (Nat.card (MulAction.orbitRel.Quotient G' D')) N.R.f n N.Nm (N.g 0) (N.g 1)
    (Pr.T u) N.rd N.sc.L hf1 hn hnN (hP.T_prime u).pos hrd0 hL s1 s4 hg0 (N.g_prime 1).pos (by
      refine ((Nat.cast_le.2 hle).trans hcount).trans ?_
      rw [hrd, hE, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [pow_two n]
      exact_mod_cast hfib')
  refine (Real.le_exp_log _).trans (Real.exp_le_exp.2 (hlog.trans ?_))
  have hG : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u) := by
    have : 1 ≤ N.g 0 * N.g 1 * Pr.T u :=
      Nat.mul_pos (Nat.mul_pos (N.g_prime 0).pos (N.g_prime 1).pos) (hP.T_prime u).pos
    exact Real.log_nonneg (by exact_mod_cast this)
  have hm : (1 : ℝ) ≤ (N.R.m : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N.R.m := by exact_mod_cast (by have := N.R.two_le_m; omega : 1 ≤ N.R.m)
    exact one_le_pow₀ this
  unfold errUnit
  calc 55 * (N.R.f : ℝ) * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u)
      = 55 * (N.R.f * 1 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u)) := by ring
    _ ≤ _ := by gcongr

/- English proof (translation)
Use `⟨55, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hyp`. Take `⟨hH, -, -, -, hmu, -, -, -, hS⟩` from `hyp`. Establish `hQ : QE sel (mu : Chr X.F X.E X.K) = ∅`. Rewrite using `[hmu]`.

Conclude with `twistPrimes_trivialTuple_empty sel Sg`. Establish `hSG : rowSG Pr sel mu = Pr.vGs`. Unfold `rowSG uSG`. Use extensionality with `w`. Rewrite using `[Finset.mem_union, hQ]`.

Simplify using the standard rewrite rules. Establish `hk : 5 ≤ N.R.k` using `by have := N.R.m_add_three_le_k; have := N.R.two_le_m; omega`. Establish `hm : 2 ≤ N.R.N N.R.m` using `by unfold Ranks.N; omega`. Use `⟨fun j hj b => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hn : 1 ≤ N.R.N j` using `by unfold Ranks.N; omega`.

Establish `hnN : N.R.N j ≤ N.Nm` using `by unfold NumDatum.Nm Ranks.N; gcongr`. Use `@card_orbits_le_exp D N X s Pr hH pl u δ CY hS _ hn hnN _ _ subset_rfl rfl (FrmG (I.levG j b) (I.levQ j b)) (ChPt (R := N.R) (Pr := Pr) sel mu u j) _ (frmAct (I.levG j b) (I.levQ j b)) DecoF.deco ?_ fun g x => ⟨(g, 1, 1), rfl⟩` and prove the remaining obligations. Introduce `x y hxy`. Use `Subtype.ext (Prod.ext hxy (funext fun P => ?_))` and prove the remaining obligations. Conclude with `absurd P.2 (Finset.eq_empty_iff_forall_notMem.1 hQ P.1)`.

Conclude with `@card_orbits_le_exp D N X s Pr hH pl u δ CY hS (N.R.N N.R.m - 1) (by omega) (Nat.sub_le _ _) ∅ _ (Finset.empty_subset _) hSG (FormG (rowTy Ch sel mu (rPsymF Ch)).inv) (RowPt Pr N.R sel mu) _ (formAct (rowTy Ch sel mu (rPsymF Ch)).inv) id Function.injective_id fun g x => ⟨(g, 1), …`. Unfold `topClassNumber`. Conclude with `card_orbits_le_exp (n := N.R.N N.R.m) hH pl u hS (le_trans (by norm_num) hm) le_rfl subset_rfl hSG id Function.injective_id fun g x => ⟨⟨(g, 1), Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, one_mem _⟩⟩, rfl⟩`.
-/
theorem classNumbers_leS : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → (∀ j ≤ N.R.m, ∀ b : I.β j, (Nat.card ((chF W sel mu I u j).mem b).Cl : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u))) ∧ (Nat.card (evGSD W Ch sel mu (rPsymF Ch) u).Cl : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) ∧ (topClassNumber Ch sel mu u : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  refine ⟨55, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hyp
  obtain ⟨hH, -, -, -, hmu, -, -, -, hS⟩ := hyp
  have hQ : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
    rw [hmu]
    exact twistPrimes_trivialTuple_empty sel Sg
  have hSG : rowSG Pr sel mu = Pr.vGs := by
    unfold rowSG uSG
    ext w
    classical
    rw [Finset.mem_union, hQ]
    simp
  have hk : 5 ≤ N.R.k := by have := N.R.m_add_three_le_k; have := N.R.two_le_m; omega
  have hm : 2 ≤ N.R.N N.R.m := by unfold Ranks.N; omega
  refine ⟨fun j hj b => ?_, ?_, ?_⟩
  · have hn : 1 ≤ N.R.N j := by unfold Ranks.N; omega
    have hnN : N.R.N j ≤ N.Nm := by unfold NumDatum.Nm Ranks.N; gcongr
    refine @card_orbits_le_exp D N X s Pr hH pl u δ CY hS _ hn hnN _ _ subset_rfl rfl (FrmG (I.levG j b) (I.levQ j b))
      (ChPt (R := N.R) (Pr := Pr) sel mu u j) _ (frmAct (I.levG j b) (I.levQ j b)) DecoF.deco ?_
      fun g x => ⟨(g, 1, 1), rfl⟩
    intro x y hxy
    refine Subtype.ext (Prod.ext hxy (funext fun P => ?_))
    exact absurd P.2 (Finset.eq_empty_iff_forall_notMem.1 hQ P.1)
  · exact @card_orbits_le_exp D N X s Pr hH pl u δ CY hS (N.R.N N.R.m - 1) (by omega) (Nat.sub_le _ _) ∅ _ (Finset.empty_subset _) hSG
      (FormG (rowTy Ch sel mu (rPsymF Ch)).inv) (RowPt Pr N.R sel mu) _ (formAct (rowTy Ch sel mu (rPsymF Ch)).inv) id
      Function.injective_id fun g x => ⟨(g, 1), rfl⟩
  · unfold topClassNumber
    exact card_orbits_le_exp (n := N.R.N N.R.m) hH pl u hS (le_trans (by norm_num) hm) le_rfl subset_rfl hSG id Function.injective_id
      fun g x => ⟨⟨(g, 1), Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, one_mem _⟩⟩, rfl⟩

end GlobalTheory.ChainClassNumbersS

end
