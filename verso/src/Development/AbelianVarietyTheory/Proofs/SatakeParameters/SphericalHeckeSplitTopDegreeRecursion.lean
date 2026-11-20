import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairMultMulRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeScalarLabelCompEqShiftDownSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeGLChartOfUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CartanExponentsNonnegMinusculeTopProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTopStep

open Formalism.L2.NTheta

/- English proof (translation)
Unfold `opOf`. Rewrite using `[← Finsupp.sum_finset_sum_index (by simp) (by intros; simp [add_smul])]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.sum_single_index (by simp)]`.
-/
theorem opOf_sum_single {D : D7} {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) {ι : Type} (s : Finset ι) (l : ι → List ℤ) (z : ι → ℂ) :
    opOf π P (∑ i ∈ s, Finsupp.single (l i) (z i)) = ∑ i ∈ s, z i • ∑ γ ∈ rep V P (l i), π γ := by
  classical
  unfold opOf
  rw [← Finsupp.sum_finset_sum_index (by simp) (by intros; simp [add_smul])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_single_index (by simp)]

/- English proof (translation)
The claim follows from `| 0, _, _, i => i.elim0 | n + 1, d, hd, i => by have ih := pos_iff_lt (fun j : Fin n => d j.succ) (fun a b h => hd (Fin.succ_le_succ_iff.2 h)) rw [List.ofFn_succ, List.filter_cons] by_cases h0 : 0 < d 0 · simp only [h0, decide_true, if_true, List.length_cons] refine Fin.cases ?_ …`.
-/
theorem pos_iff_lt : ∀ {n : ℕ} (d : Fin n → ℤ), Antitone d →
    ∀ i : Fin n, 0 < d i ↔ (i : ℕ) < ((List.ofFn d).filter fun x => 0 < x).length
  | 0, _, _, i => i.elim0
  | n + 1, d, hd, i => by
    have ih := pos_iff_lt (fun j : Fin n => d j.succ) (fun a b h => hd (Fin.succ_le_succ_iff.2 h))
    rw [List.ofFn_succ, List.filter_cons]
    by_cases h0 : 0 < d 0
    · simp only [h0, decide_true, if_true, List.length_cons]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [h0]
      · simp [ih j]
    · have hnil : (List.ofFn fun j : Fin n => d j.succ).filter (fun x => 0 < x) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        have := hd (Fin.zero_le j.succ)
        simp only [decide_eq_true_eq, not_lt]
        omega
      simp only [h0, decide_false, Bool.false_eq_true, if_false, hnil, List.length_nil]
      have := hd (Fin.zero_le i)
      constructor
      · intro h; omega
      · intro h; omega

/- English proof (translation)
Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using `[dualLab, splitLab]`. Use linear arithmetic over natural numbers and integers. Introduce `i h1 h2`. Simplify using `[dualLab, splitLab, List.getElem_reverse, List.getElem_append, List.getElem_replicate]`.
-/
theorem dualLab_splitLab (n k : ℕ) (hk : k ≤ n) :
    dualLab (splitLab n k) = List.ofFn fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0 := by
  apply List.ext_getElem
  · simp [dualLab, splitLab]; omega
  · intro i h1 h2
    simp [dualLab, splitLab, List.getElem_reverse, List.getElem_append, List.getElem_replicate]

/- English proof (translation)
Introduce `D V P hP d hd hnn _`. Take `⟨K, hK⟩` from `GlobalTheory.SphLabelOps.exists_hyp V P`. Take `⟨R0, e, f, ϖ, α0, -, hpi, h1, h2, hdp, -, -, -, hD0, -, -⟩` from `hd`. Take `⟨he, rfl⟩` from `GlobalTheory.CentralShift.split_of_primeIdem hP hpi`. Establish `hKl : ∀ k ∈ K, k ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V k` using `fun k hk => by`.

Establish `: k ∈ hyp V P` using `hK ▸ hk`. Rewrite `this` using `[GlobalTheory.DualSplitRel.hyp_eq_locPart he V]`. Conclude with `this`. Apply the tactic sequence `obtain ⟨dF, rfl⟩ : ∃ dF : Fin V.rank → ℤ, d = List.ofFn dF := ⟨fun i => d[i.1]'(by have := hD0.1; omega), by apply List.ext_getElem <;> simp [hD0.1]⟩`. Establish `hanti : Antitone dF` using `fun i j hij => by`.

Break down `hij.lt_or_eq with h | h` into its components or cases. Conclude with `List.pairwise_ofFn.1 hdp h`. Rewrite using `[h]`. Establish `hnn' : ∀ i, 0 ≤ dF i` using `fun i => hnn _ (List.mem_ofFn.2 ⟨i, rfl⟩)`. Use `set kk := ((List.ofFn dF).filter fun x => 0 < x).length with hkk`.

Establish `hk` using `pos_iff_lt dF hanti`. Establish `hkn : kk ≤ V.rank`. Use `List.length_filter_le (fun x => decide (0 < x)) (List.ofFn dF)` as an intermediate fact. Simplify using `using this`. Use `set d₁ : Fin V.rank → ℤ := fun i => if 0 < dF i then dF i - 1 else dF i with hd₁`.

Use `set aF : Fin V.rank → ℤ := fun i => if (i : ℕ) < kk then 1 else 0 with haF`. Establish `e1 : (List.ofFn dF).map (fun x => if 0 < x then x - 1 else x) = List.ofFn d₁`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Rewrite using `[e1, dualLab_splitLab _ _ hkn]`.

Take `⟨ρ, hon, hint, hdiv⟩` from `GlobalTheory.T.exists_splitPrime_GL_chart_of_unitaryGroup V P e he ϖ h1 h2`. Use `set ϖL := algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E) with hϖL`. Establish `hv : Formalism.UG.IsUnifV D.host.E P ϖL` using `(P.valuedAdicCompletion_eq_valuation' (ϖ : D.host.E)).trans ((P.valuation_of_algebraMap ϖ).trans (GlobalTheory.LatIntFacts.intValuation_uniformiser P h1 h2))`. Establish `hvO : ϖL ∈ Formalism.UG.Ov D.host.E P` using `(Formalism.UG.P.cartan_unif_lt_one D.host.E P _ hv).le`. Establish `hϖ0 : ϖL ≠ 0`.

Introduce `h0`. Use `hv` as an intermediate fact. Unfold `Formalism.UG.IsUnifV at this`. Rewrite `this` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe this`.

Set `mkD : (Fin V.rank → ℤ) → GL (Fin V.rank) (P.adicCompletion D.host.E)` to `fun a => ⟨Formalism.UG.diagPow D.host.E P ϖL a, Formalism.UG.diagPow D.host.E P ϖL (-a), by simp only [Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal, Pi.neg_apply, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, Matrix.diagonal_one], by simp only [Formalism.UG.diagPow, Matrix.di …`. Establish `hmk : ∀ a, ((mkD a : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) = Formalism.UG.diagPow D.host.E P ϖL a` using `fun a => rfl`. Establish `hdiag : ∀ g a, ρ g = mkD a → DivAt V e (ϖ : D.host.E) (List.ofFn a) g` using `fun g a h => hdiv g a 1 (one_mem _) 1 (one_mem _) (by rw [h, hmk]; simp)`. Take `⟨g, hgS, hg⟩` from `hon (mkD d₁)`. Take `⟨h, hhS, hh⟩` from `hon (mkD aF)`.

Establish `hgh : ρ (g * h) = mkD dF`. Rewrite using `[map_mul, hg, hh]`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, hmk, Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `l`. Rewrite using `[← zpow_add₀ hϖ0]`. Use `congr 1`. Use `hk l` as an intermediate fact. Use `hnn' l` as an intermediate fact.

Simplify using `only [d₁, aF]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hpi' : IsPrimeIdem P e (e + cA D e)` using `Or.inl ⟨he, rfl⟩`. Establish `pw : ∀ a : Fin V.rank → ℤ, Antitone a → (List.ofFn a).Pairwise fun x y => y ≤ x` using `fun a ha => List.pairwise_ofFn.2 fun i j hij => ha hij.le`. Establish `hS : ∀ x, Formalism.L2.Theta.SuppAt e V x → ∀ a, Antitone a → DivAt V e (ϖ : D.host.E) (List.ofFn a) x → GlobalTheory.SphLabelOps.Reps K x (rep V P (List.ofFn a))` using `fun x hx a ha hD => GlobalTheory.SphLabelOps.reps_of_sphOp hK hpi' h1 h2 hx hD (GlobalTheory.SphLabelOps.sphOp_rep (GlobalTheory.SphLabelOps.isLab_of_divAt hpi' h1 h2 (pw a ha) hx hD))`.

Establish `a₁ : Antitone d₁` using `fun i j hij => by`. Use `hanti hij` as an intermediate fact. Apply the tactic sequence `simp only [d₁]; split_ifs <;> omega`. Establish `a₂ : Antitone aF` using `fun i j hij => by`. Establish `: (i : ℕ) ≤ j` using `hij`.

Apply the tactic sequence `simp only [aF]; split_ifs <;> omega`. Establish `r₁` using `hS g hgS d₁ a₁ (hdiag g d₁ hg)`. Establish `r₂` using `hS h hhS aF a₂ (hdiag h aF hh)`. Establish `hghS : Formalism.L2.Theta.SuppAt e V (g * h)` using `GlobalTheory.SplitHecke.suppAt_mul hgS hhS`. Establish `r₀` using `hS (g * h) hghS dF hanti (hdiag _ _ hgh)`.

Take `⟨T, m, hghT, hT, hTi, hsum⟩` from `GlobalTheory.SphLabelOps.reps_mul_decomp K g h _ _ r₁ r₂`. Establish `hx : ∀ x ∈ T, Formalism.L2.Theta.SuppAt e V x ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, ∃ k₃ ∈ K, x = k₁ * g * k₂ * h * k₃`. Introduce `x hxT`. Take `⟨-, γ, hγ, γ', hγ', k₁, hk₁, k₂, hk₂, rfl⟩` from `hT x hxT`. Take `⟨a, ha, b, hb, rfl⟩` from `r₁.1 γ hγ`.

Take `⟨a', ha', b', hb', rfl⟩` from `r₂.1 γ' hγ'`. Establish `s : ∀ k ∈ K, Formalism.L2.Theta.SuppAt e V k` using `fun k hk => (hKl k hk).2`. Establish `hxe : k₁ * (a * g * b * (a' * h * b')) * k₂ = k₁ * a * g * (b * a') * h * (b' * k₂)` using `by group`. Rewrite using `[hxe]`. Use `⟨?_, k₁ * a, K.mul_mem hk₁ ha, b * a', K.mul_mem hb ha', b' * k₂, K.mul_mem hb' hk₂, rfl⟩` and prove the remaining obligations.

Establish `m` using `@GlobalTheory.SplitHecke.suppAt_mul`. Conclude with `m (m (m (m (m (s _ hk₁) (s _ ha)) hgS) (m (s _ hb) (s _ ha'))) hhS) (m (s _ hb') (s _ hk₂))`. Establish `cart : ∀ x : GA D V, ∃ a : Fin V.rank → ℤ, Antitone a ∧ ∃ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∃ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ((ρ x : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank …` using `fun x => Formalism.UG.Final.CartanDecomp D.host.E P V.rank ϖL hvO hv (ρ x)`. Use `choose cx hcx k₁x hk₁x k₂x hk₂x hcxe using cart`. Establish `hcxD : ∀ x, DivAt V e (ϖ : D.host.E) (List.ofFn (cx x)) x` using `fun x => hdiv x (cx x) _ (hk₁x x) _ (hk₂x x) (hcxe x)`.

Establish `hineq : ∀ x ∈ T, x ≠ g * h → (∀ i, 0 ≤ cx x i) ∧ (∑ i, cx x i = ∑ i, dF i ∧ ∑ i, cx x i ^ 2 < ∑ i, dF i ^ 2)`. Introduce `x hxT hne`. Take `⟨sx, k₁, hk₁, k₂, hk₂, k₃, hk₃, hxe⟩` from `hx x hxT`. Establish `key` using `GlobalTheory.T.cartanExponents_nonneg_minusculeTop_product D.host.E P V.rank ϖL hv dF kk hanti hnn' hk (ρ k₁) (hint _ (hKl _ hk₁).1) (ρ k₂) (hint _ (hKl _ hk₂).1) (ρ k₃) (hint _ (hKl _ hk₃).1) (cx x) (hcx x) _ (hk₁x x) _ (hk₂x x) (by`. Rewrite using `[← hcxe x, hxe]`.

Apply the tactic sequence `simp only [map_mul, Units.val_mul, hg, hh, hmk] <;> rfl)`. Use `⟨key.1, key.2.resolve_left fun heq => hne ?_⟩` and prove the remaining obligations. Establish `rx` using `hS x sx (cx x) (hcx x) (hcxD x)`. Rewrite `rx` using `[heq]`. Take `⟨γ, ⟨hγ, hγx⟩, -⟩` from `rx.2 x ⟨1, K.one_mem, 1, K.one_mem, by group⟩`.

Take `⟨a, ha, b, hb, hγe⟩` from `r₀.1 γ hγ`. Use `(hTi (g * h) hghT x hxT ⟨a, ha, b * (γ⁻¹ * x), K.mul_mem hb hγx, by rw [← mul_assoc, ← hγe]; group⟩).symm` and prove the remaining obligations. Use `⟨m (g * h), (hT _ hghT).1, ∑ x ∈ T.erase (g * h), Finsupp.single (List.ofFn (cx x)) (m x : ℂ), ?_, ?_⟩` and prove the remaining obligations. Introduce `d' hd'`. Take `⟨x, hxT, hd'x⟩` from `Finset.mem_biUnion.1 (Finsupp.support_finset_sum hd')`.

Take `⟨hne, hxT⟩` from `Finset.mem_erase.1 hxT`. Rewrite using `[Finset.mem_singleton.1 (Finsupp.support_single_subset hd'x)]`. Take `⟨c1, c2, c3⟩` from `hineq x hxT hne`. Use `⟨fun y hy => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hy`.

Conclude with `c1 i`. Rewrite using `[List.sum_ofFn, List.sum_ofFn]`. Conclude with `c2`. Rewrite using `[List.map_ofFn, List.map_ofFn, List.sum_ofFn, List.sum_ofFn]`. Conclude with `c3`.

Introduce `M _ _ π u hu`. Establish `hu' : ∀ k ∈ K, π k u = u` using `fun k hk => hu k (hK ▸ hk)`. Rewrite using `[GlobalTheory.SphLabelOps.opOf_single, GlobalTheory.SphLabelOps.opOf_single, GlobalTheory.SphLabelOps.opOf_single, opOf_sum_single, LinearMap.sum_apply]`. Establish `hsum'` using `hsum (fun x => if x = g * h then rep V P (List.ofFn dF) else rep V P (List.ofFn (cx x))) (fun x hxT => by`. Distinguish the cases in `hxe : x = g * h`.

Rewrite using `[if_pos hxe, hxe]`. Conclude with `r₀`. Rewrite using `[if_neg hxe]`. Conclude with `hS x (hx x hxT).1 (cx x) (hcx x) (hcxD x)) M π u hu'`. Establish `lhs : ∑ γ ∈ rep V P (List.ofFn d₁), π γ (∑ γ' ∈ rep V P (List.ofFn aF), π γ' u) = ∑ γ ∈ rep V P (List.ofFn d₁), ∑ γ' ∈ rep V P (List.ofFn aF), π (γ * γ') u`.

Use `Finset.sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun γ' _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply]`. Rewrite using `[lhs, hsum', ← Finset.add_sum_erase _ _ hghT, if_pos rfl]`.

Use `congr 1`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Use `Finset.sum_congr rfl fun x hxT => ?_` and prove the remaining obligations. Rewrite using `[if_neg (Finset.mem_erase.1 hxT).1, LinearMap.smul_apply, LinearMap.sum_apply, Nat.cast_smul_eq_nsmul]`.
-/
theorem top_step : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ d : List ℤ, IsLab V P d → (∀ x ∈ d, 0 ≤ x) → (∃ x ∈ d, 0 < x) → ∃ m : ℕ, 0 < m ∧ ∃ c : List ℤ →₀ ℂ, (∀ d' ∈ c.support, (∀ x ∈ d', 0 ≤ x) ∧ d'.sum = d.sum ∧ (d'.map fun x => x ^ 2).sum < (d.map fun x => x ^ 2).sum) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (d.map fun x => if 0 < x then x - 1 else x) 1) (opOf π P (Finsupp.single (dualLab (splitLab V.rank (d.filter fun x => 0 < x).length)) 1) u) = (m : ℂ) • opOf π P (Finsupp.single d 1) u + opOf π P c u := by
  classical
  intro D V P hP d hd hnn _
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨R0, e, f, ϖ, α0, -, hpi, h1, h2, hdp, -, -, -, hD0, -, -⟩ := hd
  obtain ⟨he, rfl⟩ := GlobalTheory.CentralShift.split_of_primeIdem hP hpi
  have hKl : ∀ k ∈ K, k ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V k := fun k hk => by
    have : k ∈ hyp V P := hK ▸ hk
    rw [GlobalTheory.DualSplitRel.hyp_eq_locPart he V] at this
    exact this
  obtain ⟨dF, rfl⟩ : ∃ dF : Fin V.rank → ℤ, d = List.ofFn dF :=
    ⟨fun i => d[i.1]'(by have := hD0.1; omega), by apply List.ext_getElem <;> simp [hD0.1]⟩
  have hanti : Antitone dF := fun i j hij => by
    rcases hij.lt_or_eq with h | h
    · exact List.pairwise_ofFn.1 hdp h
    · rw [h]
  have hnn' : ∀ i, 0 ≤ dF i := fun i => hnn _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  set kk := ((List.ofFn dF).filter fun x => 0 < x).length with hkk
  have hk := pos_iff_lt dF hanti
  have hkn : kk ≤ V.rank := by
    have := List.length_filter_le (fun x => decide (0 < x)) (List.ofFn dF)
    simpa using this
  set d₁ : Fin V.rank → ℤ := fun i => if 0 < dF i then dF i - 1 else dF i with hd₁
  set aF : Fin V.rank → ℤ := fun i => if (i : ℕ) < kk then 1 else 0 with haF
  have e1 : (List.ofFn dF).map (fun x => if 0 < x then x - 1 else x) = List.ofFn d₁ := by
    rw [List.map_ofFn]; rfl
  rw [e1, dualLab_splitLab _ _ hkn]

  obtain ⟨ρ, hon, hint, hdiv⟩ := GlobalTheory.T.exists_splitPrime_GL_chart_of_unitaryGroup V P e he ϖ h1 h2
  set ϖL := algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E) with hϖL
  have hv : Formalism.UG.IsUnifV D.host.E P ϖL :=
    (P.valuedAdicCompletion_eq_valuation' (ϖ : D.host.E)).trans
      ((P.valuation_of_algebraMap ϖ).trans (GlobalTheory.LatIntFacts.intValuation_uniformiser P h1 h2))
  have hvO : ϖL ∈ Formalism.UG.Ov D.host.E P := (Formalism.UG.P.cartan_unif_lt_one D.host.E P _ hv).le
  have hϖ0 : ϖL ≠ 0 := by
    intro h0
    have := hv
    unfold Formalism.UG.IsUnifV at this
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let mkD : (Fin V.rank → ℤ) → GL (Fin V.rank) (P.adicCompletion D.host.E) := fun a =>
    ⟨Formalism.UG.diagPow D.host.E P ϖL a, Formalism.UG.diagPow D.host.E P ϖL (-a),
      by simp only [Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal, Pi.neg_apply, ← zpow_add₀ hϖ0, add_neg_cancel,
          zpow_zero, Matrix.diagonal_one],
      by simp only [Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal, Pi.neg_apply, ← zpow_add₀ hϖ0, neg_add_cancel,
          zpow_zero, Matrix.diagonal_one]⟩
  have hmk : ∀ a, ((mkD a : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
      Formalism.UG.diagPow D.host.E P ϖL a := fun a => rfl
  have hdiag : ∀ g a, ρ g = mkD a → DivAt V e (ϖ : D.host.E) (List.ofFn a) g := fun g a h =>
    hdiv g a 1 (one_mem _) 1 (one_mem _) (by rw [h, hmk]; simp)
  obtain ⟨g, hgS, hg⟩ := hon (mkD d₁)
  obtain ⟨h, hhS, hh⟩ := hon (mkD aF)
  have hgh : ρ (g * h) = mkD dF := by
    rw [map_mul, hg, hh]
    apply Units.ext
    simp only [Units.val_mul, hmk, Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal]
    congr 1
    funext l
    rw [← zpow_add₀ hϖ0]
    congr 1
    have := hk l
    have := hnn' l
    simp only [d₁, aF]
    split_ifs <;> omega
  have hpi' : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have pw : ∀ a : Fin V.rank → ℤ, Antitone a → (List.ofFn a).Pairwise fun x y => y ≤ x :=
    fun a ha => List.pairwise_ofFn.2 fun i j hij => ha hij.le
  have hS : ∀ x, Formalism.L2.Theta.SuppAt e V x → ∀ a, Antitone a → DivAt V e (ϖ : D.host.E) (List.ofFn a) x →
      GlobalTheory.SphLabelOps.Reps K x (rep V P (List.ofFn a)) := fun x hx a ha hD =>
    GlobalTheory.SphLabelOps.reps_of_sphOp hK hpi' h1 h2 hx hD
      (GlobalTheory.SphLabelOps.sphOp_rep (GlobalTheory.SphLabelOps.isLab_of_divAt hpi' h1 h2 (pw a ha) hx hD))
  have a₁ : Antitone d₁ := fun i j hij => by
    have := hanti hij
    simp only [d₁]; split_ifs <;> omega
  have a₂ : Antitone aF := fun i j hij => by
    have : (i : ℕ) ≤ j := hij
    simp only [aF]; split_ifs <;> omega
  have r₁ := hS g hgS d₁ a₁ (hdiag g d₁ hg)
  have r₂ := hS h hhS aF a₂ (hdiag h aF hh)
  have hghS : Formalism.L2.Theta.SuppAt e V (g * h) := GlobalTheory.SplitHecke.suppAt_mul hgS hhS
  have r₀ := hS (g * h) hghS dF hanti (hdiag _ _ hgh)
  obtain ⟨T, m, hghT, hT, hTi, hsum⟩ := GlobalTheory.SphLabelOps.reps_mul_decomp K g h _ _ r₁ r₂

  have hx : ∀ x ∈ T, Formalism.L2.Theta.SuppAt e V x ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, ∃ k₃ ∈ K, x = k₁ * g * k₂ * h * k₃ := by
    intro x hxT
    obtain ⟨-, γ, hγ, γ', hγ', k₁, hk₁, k₂, hk₂, rfl⟩ := hT x hxT
    obtain ⟨a, ha, b, hb, rfl⟩ := r₁.1 γ hγ
    obtain ⟨a', ha', b', hb', rfl⟩ := r₂.1 γ' hγ'
    have s : ∀ k ∈ K, Formalism.L2.Theta.SuppAt e V k := fun k hk => (hKl k hk).2
    have hxe : k₁ * (a * g * b * (a' * h * b')) * k₂ = k₁ * a * g * (b * a') * h * (b' * k₂) := by group
    rw [hxe]
    refine ⟨?_, k₁ * a, K.mul_mem hk₁ ha, b * a', K.mul_mem hb ha', b' * k₂, K.mul_mem hb' hk₂, rfl⟩
    have m := @GlobalTheory.SplitHecke.suppAt_mul
    exact m (m (m (m (m (s _ hk₁) (s _ ha)) hgS) (m (s _ hb) (s _ ha'))) hhS) (m (s _ hb') (s _ hk₂))

  have cart : ∀ x : GA D V, ∃ a : Fin V.rank → ℤ, Antitone a ∧
      ∃ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∃ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P),
        ((ρ x : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
          (k₁ : Matrix (Fin V.rank) (Fin V.rank) _) * Formalism.UG.diagPow D.host.E P ϖL a * (k₂ : Matrix (Fin V.rank) (Fin V.rank) _) :=
    fun x => Formalism.UG.Final.CartanDecomp D.host.E P V.rank ϖL hvO hv (ρ x)
  choose cx hcx k₁x hk₁x k₂x hk₂x hcxe using cart
  have hcxD : ∀ x, DivAt V e (ϖ : D.host.E) (List.ofFn (cx x)) x := fun x =>
    hdiv x (cx x) _ (hk₁x x) _ (hk₂x x) (hcxe x)

  have hineq : ∀ x ∈ T, x ≠ g * h → (∀ i, 0 ≤ cx x i) ∧
      (∑ i, cx x i = ∑ i, dF i ∧ ∑ i, cx x i ^ 2 < ∑ i, dF i ^ 2) := by
    intro x hxT hne
    obtain ⟨sx, k₁, hk₁, k₂, hk₂, k₃, hk₃, hxe⟩ := hx x hxT
    have key := GlobalTheory.T.cartanExponents_nonneg_minusculeTop_product D.host.E P V.rank ϖL hv dF kk hanti hnn' hk (ρ k₁) (hint _ (hKl _ hk₁).1)
      (ρ k₂) (hint _ (hKl _ hk₂).1) (ρ k₃) (hint _ (hKl _ hk₃).1) (cx x) (hcx x) _ (hk₁x x) _ (hk₂x x) (by
        rw [← hcxe x, hxe]
        simp only [map_mul, Units.val_mul, hg, hh, hmk] <;> rfl)
    refine ⟨key.1, key.2.resolve_left fun heq => hne ?_⟩
    have rx := hS x sx (cx x) (hcx x) (hcxD x)
    rw [heq] at rx
    obtain ⟨γ, ⟨hγ, hγx⟩, -⟩ := rx.2 x ⟨1, K.one_mem, 1, K.one_mem, by group⟩
    obtain ⟨a, ha, b, hb, hγe⟩ := r₀.1 γ hγ
    refine (hTi (g * h) hghT x hxT ⟨a, ha, b * (γ⁻¹ * x), K.mul_mem hb hγx, by rw [← mul_assoc, ← hγe]; group⟩).symm
  refine ⟨m (g * h), (hT _ hghT).1, ∑ x ∈ T.erase (g * h), Finsupp.single (List.ofFn (cx x)) (m x : ℂ), ?_, ?_⟩
  · intro d' hd'
    obtain ⟨x, hxT, hd'x⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hd')
    obtain ⟨hne, hxT⟩ := Finset.mem_erase.1 hxT
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hd'x)]
    obtain ⟨c1, c2, c3⟩ := hineq x hxT hne
    refine ⟨fun y hy => ?_, ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      exact c1 i
    · rw [List.sum_ofFn, List.sum_ofFn]; exact c2
    · rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn, List.sum_ofFn]; exact c3
  · intro M _ _ π u hu
    have hu' : ∀ k ∈ K, π k u = u := fun k hk => hu k (hK ▸ hk)
    rw [GlobalTheory.SphLabelOps.opOf_single, GlobalTheory.SphLabelOps.opOf_single, GlobalTheory.SphLabelOps.opOf_single, opOf_sum_single,
      LinearMap.sum_apply]
    have hsum' := hsum (fun x => if x = g * h then rep V P (List.ofFn dF) else rep V P (List.ofFn (cx x)))
      (fun x hxT => by
        by_cases hxe : x = g * h
        · rw [if_pos hxe, hxe]; exact r₀
        · rw [if_neg hxe]; exact hS x (hx x hxT).1 (cx x) (hcx x) (hcxD x)) M π u hu'
    have lhs : ∑ γ ∈ rep V P (List.ofFn d₁), π γ (∑ γ' ∈ rep V P (List.ofFn aF), π γ' u) =
        ∑ γ ∈ rep V P (List.ofFn d₁), ∑ γ' ∈ rep V P (List.ofFn aF), π (γ * γ') u := by
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun γ' _ => ?_
      rw [map_mul, Module.End.mul_apply]
    rw [lhs, hsum', ← Finset.add_sum_erase _ _ hghT, if_pos rfl]
    congr 1
    · rw [Nat.cast_smul_eq_nsmul]
    · refine Finset.sum_congr rfl fun x hxT => ?_
      rw [if_neg (Finset.mem_erase.1 hxT).1, LinearMap.smul_apply, LinearMap.sum_apply, Nat.cast_smul_eq_nsmul]

end GlobalTheory.SplitTopStep
