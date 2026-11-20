import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAevalOfWeighted
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainStatementOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOfHasChainAtPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TerminalChainOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantChainOfPublishedInputsStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Whole4

open Formalism.BasicNotions.DV GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison

/- English proof (translation)
The claim follows from `GlobalTheory.T.chainW_of_alteration_prismatic`.
-/
theorem chains_whole : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd → ChainWSt := GlobalTheory.T.chainW_of_alteration_prismatic

/- English proof (translation)
The claim follows from `GlobalTheory.T.local_of_has_chain_at_prime`.
-/
theorem localW_of_chain : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) [Fact p.Prime] (hp : p.Prime)
    (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ),
    HasChainW z jc → LocalW (mdlOf z jc) := GlobalTheory.T.local_of_has_chain_at_prime

/- English proof (translation)
The claim follows from `GlobalTheory.T.terminal_chain_of_published_inputs`.
-/
theorem termW_all : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd → TermWSt := GlobalTheory.T.terminal_chain_of_published_inputs

/- English proof (translation)
The claim follows from `GlobalTheory.T.constant_chain_of_hypotheses`.
-/
theorem consW_all : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd → ConsWSt := GlobalTheory.T.constant_chain_of_hypotheses

/- English proof (translation)
Establish `hT : 0 < Fintype.card D.what₂.Tau` using `Fintype.card_pos_iff.2 ⟨D.eTau.symm 1⟩`. Establish `hN : 2 ≤ O.Y.N`. Use `O.indef` as an intermediate fact. Express the relevant statement in the definitionally equal form `2 ≤ O.N`. Use linear arithmetic over natural numbers and integers.

Unfold `dimFl`. Establish `: 1 ≤ O.Y.N * (O.Y.N - 1) / 2`. Rewrite using `[Nat.le_div_iff_mul_le (by norm_num)]`. Establish `: 2 ≤ O.Y.N - 1 + 1` using `by omega`. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_le_dimFl {D : D7} (O : Setup D) : 1 ≤ dimFl D.what₂.Tau O.Y.N := by
  have hT : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos_iff.2 ⟨D.eTau.symm 1⟩
  have hN : 2 ≤ O.Y.N := by
    have := O.indef
    change 2 ≤ O.N
    omega
  unfold dimFl
  have : 1 ≤ O.Y.N * (O.Y.N - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : 2 ≤ O.Y.N - 1 + 1 := by omega
    nlinarith
  nlinarith

/- English proof (translation)
Rewrite using `[rename_monomial]`. Use `isWeightedHomogeneous_monomial _ _ _ ?_` and prove the remaining obligations. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]`. Rewrite using `[Finsupp.degree_eq_weight_one, Finsupp.weight_apply]`. Both sides reduce to the same expression.
-/
theorem homog_rename_dr {Tau : Type} [Fintype Tau] {N : ℕ} (d : Rt Tau N →₀ ℕ) :
    (rename (fun x => (Sum.inl (false, x) : Vm Tau N)) (monomial d (1 : ℚ))).IsWeightedHomogeneous
      (Formalism.MainNotions.LatticeTransfer.wt Tau N) d.degree := by
  rw [rename_monomial]
  refine isWeightedHomogeneous_monomial _ _ _ ?_
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]
  rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply]
  rfl

/- English proof (translation)
Simplify using `only [tagDR, Formalism.MainNotions.LatticeTransfer.toR, AlgHom.coe_toRingHom]`. Rewrite using `[map_rename]`.
-/
theorem tagDR_toR {Tau : Type} [Fintype Tau] {N : ℕ} (G : MvPolynomial (Rt Tau N) ℚ) :
    tagDR Tau N (Formalism.MainNotions.LatticeTransfer.toR G) = Formalism.MainNotions.LatticeTransfer.toR (rename (fun x => (Sum.inl (false, x) : Vm Tau N)) G) := by
  simp only [tagDR, Formalism.MainNotions.LatticeTransfer.toR, AlgHom.coe_toRingHom]
  rw [map_rename]

/- English proof (translation)
Rewrite using `[← tagDR_toR]`. Express the relevant statement in the definitionally equal form `(collapse D N).comp (tagDR D.what₂.Tau N) _ = _`. Establish `: (collapse D N).comp (tagDR D.what₂.Tau N) = AlgHom.id ℝ _`. Use extensionality with `x`. Simplify using `[collapse, tagDR]`.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem collapse_toR {D : D7} {N : ℕ} (G : MvPolynomial (Rt D.what₂.Tau N) ℚ) :
    collapse D N (Formalism.MainNotions.LatticeTransfer.toR (rename (fun x => (Sum.inl (false, x) : Vm D.what₂.Tau N)) G)) = Formalism.MainNotions.LatticeTransfer.toR G := by
  rw [← tagDR_toR]
  change (collapse D N).comp (tagDR D.what₂.Tau N) _ = _
  have : (collapse D N).comp (tagDR D.what₂.Tau N) = AlgHom.id ℝ _ := by
    ext x; simp [collapse, tagDR]
  rw [this]; rfl

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hdim` using `one_le_dimFl O`. Take `⟨ι, _, w, W, hW, jc, z, hpin, hsum, hT⟩` from `termW_all h2 hH hRA hSW hPD D O hC p`. Use `set m := dimFl D.what₂.Tau O.Y.N - 1 with hm`. Use `set G' : MvPolynomial (Vm D.what₂.Tau O.Y.N) ℚ := rename (fun x => Sum.inl (false, x)) (monomial d (1 : ℚ)) with hG'`.

Establish `hG'h : G'.IsWeightedHomogeneous (Formalism.MainNotions.LatticeTransfer.wt D.what₂.Tau O.Y.N) m` using `hd ▸ homog_rename_dr d`. Establish `e1 : tagDR D.what₂.Tau O.Y.N (Formalism.MainNotions.LatticeTransfer.toR (monomial d (1 : ℚ))) = Formalism.MainNotions.LatticeTransfer.toR G'` using `tagDR_toR _`. Establish `e2 : collapse D O.Y.N (Formalism.MainNotions.LatticeTransfer.toR G') = Formalism.MainNotions.LatticeTransfer.toR (monomial d (1 : ℚ))` using `collapse_toR _`. Establish `hterm` using `hT Sx R hR 2 m (by norm_num) (by omega) G' hG'h`. Establish `hloc : ∀ la, chk (mdlOf (z la) (jc la)).lieW 2 (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G') + chk (mdlOf (z la) (jc la)).omW 2 (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G') = (((p : ℝ …` using `fun la => localW_of_chain D _ _ _ _ _ p Fact.out (W la) (hW la) (z la) (jc la) (chains_whole hX h2 hH hRA hSW hPD D O hC p (W la) (hW la) (jc la) (hpin la) (z la)) 2 (by norm_num) m (show m + 2 = dimFl D.what₂.Tau O.Y.N + 1 by omega) _ (GlobalTheory.HodgeTateGlobal.homog_evV _ _ …`.

Establish `hcons : ∀ la, chDiv (mdlOf (z la) (jc la)).lieW.x 1 (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G') / ((mdlOf (z la) (jc la)).cov : ℝ) = O.Y.chern (chLieA D O.Y.N O.Y.j 1 * collapse D O.Y.N (Formalism.MainNotions.LatticeTransfer.toR G …` using `fun la => consW_all h2 hH hRA hSW hPD D O hC p (W la) (hW la) (jc la) (hpin la) (z la) m (show m + 1 = dimFl D.what₂.Tau O.Y.N by omega) G' hG'h`. Rewrite using `[e1]`. Express the relevant statement in the definitionally equal form `O.Y.arMix Sx R p (Formalism.MainNotions.LatticeTransfer.dCh D.what₂.Tau O.Y.N 2 * Formalism.MainNotions.LatticeTransfer.toR G') = _`. Rewrite using `[hterm]`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`.

Establish `hs : ∀ la, w la * ((chk (mdlOf (z la) (jc la)).lieW 2 (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G') + chk (mdlOf (z la) (jc la)).omW 2 (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G')) / …` using `fun la => by`. Rewrite using `[hloc la, mul_div_assoc, hcons la]`. Use `(congrArg (fun s => Real.log p * s) (Finset.sum_congr rfl fun la _ => hs la)).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, hsum, one_mul, e2]`. Establish `h1 : (p : ℝ) - 1 ≠ 0` using `by linarith`.

Establish `h2' : (p : ℝ) ^ 2 - 1 ≠ 0` using `by nlinarith`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourth_power_monomial_vanish (hX : GlobalTheory.CovTop.HypothesesXH) (h2 : Hypotheses2) (hH : HypothesesH) (hRA : RegularAlteration) (hSW : ScholzeWeinsteinB)
    (hPD : PrismaticDieudonnePerfd) {D : D7} (O : Setup D) (hC : O.Core) (Sx : Finset ℕ) (R : ℝ) (hR : 2 ≤ R)
    (p : ℕ) (hp : p.Prime) (d : Rt D.what₂.Tau O.Y.N →₀ ℕ) (hd : d.degree = dimFl D.what₂.Tau O.Y.N - 1) :
    O.Y.arMix Sx R p ((X (Sum.inr (false, 2)) - X (Sum.inr (true, 2))) *
        tagDR D.what₂.Tau _ (Formalism.MainNotions.LatticeTransfer.toR (monomial d (1 : ℚ)))) =
      -(Real.log p * ((p : ℝ) / ((p : ℝ) ^ 2 - 1)) *
        O.Y.chern (chLieA D _ O.Y.j 1 * Formalism.MainNotions.LatticeTransfer.toR (monomial d (1 : ℚ)))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdim := one_le_dimFl O
  obtain ⟨ι, _, w, W, hW, jc, z, hpin, hsum, hT⟩ := termW_all h2 hH hRA hSW hPD D O hC p
  set m := dimFl D.what₂.Tau O.Y.N - 1 with hm
  set G' : MvPolynomial (Vm D.what₂.Tau O.Y.N) ℚ := rename (fun x => Sum.inl (false, x)) (monomial d (1 : ℚ)) with hG'
  have hG'h : G'.IsWeightedHomogeneous (Formalism.MainNotions.LatticeTransfer.wt D.what₂.Tau O.Y.N) m := hd ▸ homog_rename_dr d
  have e1 : tagDR D.what₂.Tau O.Y.N (Formalism.MainNotions.LatticeTransfer.toR (monomial d (1 : ℚ))) = Formalism.MainNotions.LatticeTransfer.toR G' := tagDR_toR _
  have e2 : collapse D O.Y.N (Formalism.MainNotions.LatticeTransfer.toR G') = Formalism.MainNotions.LatticeTransfer.toR (monomial d (1 : ℚ)) := collapse_toR _
  have hterm := hT Sx R hR 2 m (by norm_num) (by omega) G' hG'h
  have hloc : ∀ la, chk (mdlOf (z la) (jc la)).lieW 2 (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G') +
      chk (mdlOf (z la) (jc la)).omW 2 (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G') =
      (((p : ℝ) ^ 2 - 1)⁻¹ - ((p : ℝ) - 1)⁻¹) *
        chDiv (mdlOf (z la) (jc la)).lieW.x 1 (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G') :=
    fun la => localW_of_chain D _ _ _ _ _ p Fact.out (W la) (hW la) (z la) (jc la)
      (chains_whole hX h2 hH hRA hSW hPD D O hC p (W la) (hW la) (jc la) (hpin la) (z la)) 2 (by norm_num) m (show m + 2 = dimFl D.what₂.Tau O.Y.N + 1 by omega) _
      (GlobalTheory.HodgeTateGlobal.homog_evV _ _ hG'h)
  have hcons : ∀ la, chDiv (mdlOf (z la) (jc la)).lieW.x 1
      (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G') / ((mdlOf (z la) (jc la)).cov : ℝ) =
      O.Y.chern (chLieA D O.Y.N O.Y.j 1 * collapse D O.Y.N (Formalism.MainNotions.LatticeTransfer.toR G')) :=
    fun la => consW_all h2 hH hRA hSW hPD D O hC p (W la) (hW la) (jc la) (hpin la) (z la) m (show m + 1 = dimFl D.what₂.Tau O.Y.N by omega) G' hG'h
  rw [e1]
  change O.Y.arMix Sx R p (Formalism.MainNotions.LatticeTransfer.dCh D.what₂.Tau O.Y.N 2 * Formalism.MainNotions.LatticeTransfer.toR G') = _
  rw [hterm]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hs : ∀ la, w la * ((chk (mdlOf (z la) (jc la)).lieW 2
        (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G') +
      chk (mdlOf (z la) (jc la)).omW 2 (Formalism.MainNotions.LatticeTransfer.evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G')) /
        ((mdlOf (z la) (jc la)).cov : ℝ)) =
      w la * ((((p : ℝ) ^ 2 - 1)⁻¹ - ((p : ℝ) - 1)⁻¹) *
        O.Y.chern (chLieA D O.Y.N O.Y.j 1 * collapse D O.Y.N (Formalism.MainNotions.LatticeTransfer.toR G'))) := fun la => by
    rw [hloc la, mul_div_assoc, hcons la]
  refine (congrArg (fun s => Real.log p * s) (Finset.sum_congr rfl fun la _ => hs la)).trans ?_
  rw [← Finset.sum_mul, hsum, one_mul, e2]
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2' : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

/- English proof (translation)
Establish `e : (monomial d r : MvPolynomial (Rt D.what₂.Tau O.Y.N) ℝ) = r • Formalism.MainNotions.LatticeTransfer.toR (monomial d (1 : ℚ))`. Simplify using `[Formalism.MainNotions.LatticeTransfer.toR, smul_monomial]`. Rewrite using `[e, map_smul, mul_smul_comm, map_smul, mul_smul_comm, map_smul, fourth_power_monomial_vanish hX h2 hH hRA hSW hPD O hC Sx R hR p hp d hd, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourth_power_monomial_real (hX : GlobalTheory.CovTop.HypothesesXH) (h2 : Hypotheses2) (hH : HypothesesH) (hRA : RegularAlteration) (hSW : ScholzeWeinsteinB)
    (hPD : PrismaticDieudonnePerfd) {D : D7} (O : Setup D) (hC : O.Core) (Sx : Finset ℕ) (R : ℝ) (hR : 2 ≤ R)
    (p : ℕ) (hp : p.Prime) (d : Rt D.what₂.Tau O.Y.N →₀ ℕ) (hd : d.degree = dimFl D.what₂.Tau O.Y.N - 1) (r : ℝ) :
    O.Y.arMix Sx R p ((X (Sum.inr (false, 2)) - X (Sum.inr (true, 2))) * tagDR D.what₂.Tau _ (monomial d r)) =
      -(Real.log p * ((p : ℝ) / ((p : ℝ) ^ 2 - 1)) * O.Y.chern (chLieA D _ O.Y.j 1 * monomial d r)) := by
  have e : (monomial d r : MvPolynomial (Rt D.what₂.Tau O.Y.N) ℝ) = r • Formalism.MainNotions.LatticeTransfer.toR (monomial d (1 : ℚ)) := by
    simp [Formalism.MainNotions.LatticeTransfer.toR, smul_monomial]
  rw [e, map_smul, mul_smul_comm, map_smul, mul_smul_comm, map_smul,
    fourth_power_monomial_vanish hX h2 hH hRA hSW hPD O hC Sx R hR p hp d hd, smul_eq_mul, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `hX h2 hH hRA hSW hPD D O hC _ _ _ _ _ Sx R hR p hp Q hQ`. Use `conv_lhs => rw [Q.as_sum]`. Use `conv_rhs => rw [Q.as_sum]`. Simplify using `only [map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations.

Establish `hdeg : d.degree = dimFl D.what₂.Tau O.Y.N - 1`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `hQ (mem_support_iff.1 hd)`. Conclude with `fourth_power_monomial_real hX h2 hH hRA hSW hPD O hC Sx R hR p hp d hdeg _`.
-/
theorem main : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd →
    OnObj fun _ O _ _ _ _ => PrimeLocalCondition O.Y := by
  intro hX h2 hH hRA hSW hPD D O hC _ _ _ _ _ Sx R hR p hp Q hQ
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  simp only [map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = dimFl D.what₂.Tau O.Y.N - 1 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hQ (mem_support_iff.1 hd)
  exact fourth_power_monomial_real hX h2 hH hRA hSW hPD O hC Sx R hR p hp d hdeg _

end GlobalTheory.Whole4

end
