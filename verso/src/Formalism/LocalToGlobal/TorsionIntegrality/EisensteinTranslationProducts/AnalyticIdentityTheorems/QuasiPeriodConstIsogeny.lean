import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F
namespace S2IsogenyPsi

def dom (L : PeriodPair) (α : ℂ) : Set ℂ := {z | α * z ∉ L.lattice}

/- English proof (translation)
Establish `h1 : IsClosed ((fun z => α * z) ⁻¹' (L.lattice : Set ℂ))` using `L.isClosed_lattice.preimage (continuous_const.mul continuous_id)`. Conclude with `h1.isOpen_compl`.
-/
lemma isOpen_dom (L : PeriodPair) (α : ℂ) : IsOpen (dom L α) := by
  have h1 : IsClosed ((fun z => α * z) ⁻¹' (L.lattice : Set ℂ)) :=
    L.isClosed_lattice.preimage (continuous_const.mul continuous_id)
  exact h1.isOpen_compl

/- English proof (translation)
Establish `hc : (L.lattice : Set ℂ).Countable`. Establish `hsub : (L.lattice : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂)`. Introduce `x hx`. Take `⟨m, n, h⟩` from `PeriodPair.mem_lattice.mp hx`. Conclude with `⟨(m, n), h⟩`.

Conclude with `(Set.countable_range _).mono hsub`. Establish `hc' : ((fun z => α * z) ⁻¹' (L.lattice : Set ℂ)).Countable` using `hc.preimage (mul_right_injective₀ hα)`. Establish `hrank : 1 < Module.rank ℝ ℂ` using `by first`. Consider the case `(rw [Complex.rank_real_complex]; exact one_lt_two)`. Consider the case `(rw [Complex.rank_real_complex]; norm_num)`.

Consider the case `simp [Complex.rank_real_complex]`. Establish `hconn : IsConnected ((fun z => α * z) ⁻¹' (L.lattice : Set ℂ))ᶜ` using `by first`. Consider the case `exact Set.Countable.isConnected_compl_of_one_lt_rank hrank hc'`. Consider the case `exact (Set.Countable.isPathConnected_compl_of_one_lt_rank hrank hc').isConnected`. Conclude with `hconn.isPreconnected`.
-/
lemma isPreconnected_dom (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) : IsPreconnected (dom L α) := by
  have hc : (L.lattice : Set ℂ).Countable := by
    have hsub : (L.lattice : Set ℂ) ⊆
        Set.range (fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂) := by
      intro x hx
      obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hx
      exact ⟨(m, n), h⟩
    exact (Set.countable_range _).mono hsub
  have hc' : ((fun z => α * z) ⁻¹' (L.lattice : Set ℂ)).Countable :=
    hc.preimage (mul_right_injective₀ hα)
  have hrank : 1 < Module.rank ℝ ℂ := by
    first
      | (rw [Complex.rank_real_complex]; exact one_lt_two)
      | (rw [Complex.rank_real_complex]; norm_num)
      | simp [Complex.rank_real_complex]
  have hconn : IsConnected ((fun z => α * z) ⁻¹' (L.lattice : Set ℂ))ᶜ := by
    first
      | exact Set.Countable.isConnected_compl_of_one_lt_rank hrank hc'
      | exact (Set.Countable.isPathConnected_compl_of_one_lt_rank hrank hc').isConnected
  exact hconn.isPreconnected

/- English proof (translation)
Introduce `hz'` and use `hz (hst z hz')`.
-/
lemma notMem_of_dom {L : PeriodPair} {α z : ℂ} (hst : MulStable L α) (hz : α * z ∉ L.lattice) :
    z ∉ L.lattice := fun hz' => hz (hst z hz')

/- English proof (translation)
Introduce `h`. Apply `hz` to reduce the goal to its premises. Establish `e : α * z = α * (z + P) - α * P` using `by ring`. Rewrite using `[e]`. Conclude with `L.lattice.sub_mem h hP`.
-/
lemma add_dom {L : PeriodPair} {α z P : ℂ} (hP : α * P ∈ L.lattice) (hz : α * z ∉ L.lattice) :
    α * (z + P) ∉ L.lattice := by
  intro h
  apply hz
  have e : α * z = α * (z + P) - α * P := by ring
  rw [e]
  exact L.lattice.sub_mem h hP

def psi (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (z : ℂ) : ℂ :=
  α * wZeta L (α * z) - wZeta L z - ∑ P ∈ S, wZeta L (z + P) - (∑ P ∈ S, L.weierstrassP P) * z

/- English proof (translation)
Establish `hz0 : z ∉ L.lattice` using `notMem_of_dom hst hz`. Establish `hA : HasDerivAt (fun w => α * wZeta L (α * w)) (α * (-(L.weierstrassP (α * z)) * (α * 1))) z` using `((hd L (α * z) hz).comp z ((hasDerivAt_id' z).const_mul α)).const_mul α`. Establish `hB : HasDerivAt (wZeta L) (-(L.weierstrassP z)) z` using `hd L z hz0`. Establish `hC : HasDerivAt (fun w => ∑ P ∈ S, wZeta L (w + P)) (∑ P ∈ S, -(L.weierstrassP (z + P))) z`. Establish `hC' : ∀ P ∈ S, HasDerivAt (fun w => wZeta L (w + P)) (-(L.weierstrassP (z + P))) z`.

Introduce `P hPS`. Establish `hPz : z + P ∉ L.lattice` using `notMem_of_dom hst (add_dom (hS.1 P hPS).1 hz)`. Conclude with `(hd L (z + P) hPz).comp_add_const z P`. Use `first`. Consider the case `exact HasDerivAt.fun_sum hC'`.

Consider the case `(have h5 := HasDerivAt.sum hC'`. Rewrite `h5` using `[Finset.sum_fn]`. Conclude with `h5)`. Establish `hD : HasDerivAt (fun w => (∑ P ∈ S, L.weierstrassP P) * w) ((∑ P ∈ S, L.weierstrassP P) * 1) z` using `(hasDerivAt_id' z).const_mul _`. Establish `hall` using `((hA.sub hB).sub hC).sub hD`.

Establish `hiso` using `hP L α S hα hst hS z hz`. Rewrite `hiso` using `[Finset.sum_sub_distrib]`. Rewrite `hall` using `[Finset.sum_neg_distrib]`. Use `first`. Consider the case `(refine hall.congr_deriv ?_`.

Take the linear combination `-hiso)`. Consider the case `(convert hall using 1`. Take the linear combination `hiso)`.
-/
lemma hasDerivAt_psi (hP : IsogenyP) (hd : ZetaHasDeriv) (L : PeriodPair) (α : ℂ) (S : Finset ℂ)
    (hα : α ≠ 0) (hst : MulStable L α) (hS : IsKerReps L α S) (z : ℂ) (hz : α * z ∉ L.lattice) :
    HasDerivAt (psi L α S) 0 z := by
  have hz0 : z ∉ L.lattice := notMem_of_dom hst hz
  have hA : HasDerivAt (fun w => α * wZeta L (α * w)) (α * (-(L.weierstrassP (α * z)) * (α * 1))) z :=
    ((hd L (α * z) hz).comp z ((hasDerivAt_id' z).const_mul α)).const_mul α
  have hB : HasDerivAt (wZeta L) (-(L.weierstrassP z)) z := hd L z hz0
  have hC : HasDerivAt (fun w => ∑ P ∈ S, wZeta L (w + P)) (∑ P ∈ S, -(L.weierstrassP (z + P))) z := by
    have hC' : ∀ P ∈ S, HasDerivAt (fun w => wZeta L (w + P)) (-(L.weierstrassP (z + P))) z := by
      intro P hPS
      have hPz : z + P ∉ L.lattice := notMem_of_dom hst (add_dom (hS.1 P hPS).1 hz)
      exact (hd L (z + P) hPz).comp_add_const z P
    first
      | exact HasDerivAt.fun_sum hC'
      | (have h5 := HasDerivAt.sum hC'
         rw [Finset.sum_fn] at h5
         exact h5)
  have hD : HasDerivAt (fun w => (∑ P ∈ S, L.weierstrassP P) * w) ((∑ P ∈ S, L.weierstrassP P) * 1) z :=
    (hasDerivAt_id' z).const_mul _
  have hall := ((hA.sub hB).sub hC).sub hD
  have hiso := hP L α S hα hst hS z hz
  rw [Finset.sum_sub_distrib] at hiso
  rw [Finset.sum_neg_distrib] at hall
  first
    | (refine hall.congr_deriv ?_
       linear_combination -hiso)
    | (convert hall using 1
       linear_combination hiso)

/- English proof (translation)
Establish `hdiff : DifferentiableOn ℂ (psi L α S) (dom L α)` using `fun w hw => (hasDerivAt_psi hP hd L α S hα hst hS w hw).differentiableAt.differentiableWithinAt`. Establish `hder : Set.EqOn (deriv (psi L α S)) 0 (dom L α)` using `fun w hw => (hasDerivAt_psi hP hd L α S hα hst hS w hw).deriv`. Conclude with `(isOpen_dom L α).is_const_of_deriv_eq_zero (isPreconnected_dom L α hα) hdiff hder hx hy`.
-/
lemma psi_const (hP : IsogenyP) (hd : ZetaHasDeriv) (L : PeriodPair) (α : ℂ) (S : Finset ℂ)
    (hα : α ≠ 0) (hst : MulStable L α) (hS : IsKerReps L α S) {x y : ℂ}
    (hx : α * x ∉ L.lattice) (hy : α * y ∉ L.lattice) : psi L α S x = psi L α S y := by
  have hdiff : DifferentiableOn ℂ (psi L α S) (dom L α) := fun w hw =>
    (hasDerivAt_psi hP hd L α S hα hst hS w hw).differentiableAt.differentiableWithinAt
  have hder : Set.EqOn (deriv (psi L α S)) 0 (dom L α) := fun w hw =>
    (hasDerivAt_psi hP hd L α S hα hst hS w hw).deriv
  exact (isOpen_dom L α).is_const_of_deriv_eq_zero (isPreconnected_dom L α hα) hdiff hder hx hy

/- English proof (translation)
Establish `hhalf : L.ω₁ / 2 ∉ L.lattice`. Introduce `h`. Take `⟨p, q, hpq⟩` from `PeriodPair.mem_lattice.mp h`. Establish `hli` using `L.indep`. Rewrite `hli` using `[LinearIndependent.pair_iff]`.

Take `⟨h1, h2⟩` from `hli ((p : ℝ) - 1 / 2) (q : ℝ) (by`. Simplify using `only [Complex.real_smul]`. Use `push_cast`. Take the linear combination `hpq)`. Establish `h3 : (2 : ℝ) * p = 1` using `by linarith`.

Establish `h2p : (2 * p : ℤ) = 1` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers. Establish `hax : α * (L.ω₁ / 2 / α) = L.ω₁ / 2` using `by field_simp`. Take `⟨x, hx⟩ : ∃ x, α * x ∉ L.lattice` from `⟨L.ω₁ / 2 / α, by rw [hax]; exact hhalf⟩`. Establish `hx0 : x ∉ L.lattice` using `notMem_of_dom hst hx`.

Establish `hαω : α * ω ∈ L.lattice` using `hst ω hω`. Establish `hy : α * (x + ω) ∉ L.lattice` using `add_dom hαω hx`. Establish `hc` using `psi_const hP hd L α S hα hst hS hy hx`. Establish `hsum : ∑ P ∈ S, wZeta L (x + ω + P) = ∑ P ∈ S, (wZeta L (x + P) + wEta L ω)`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `P hPS`. Establish `hxP : x + P ∉ L.lattice` using `notMem_of_dom hst (add_dom (hS.1 P hPS).1 hx)`. Rewrite using `[show x + ω + P = x + P + ω by ring, hq L ω (x + P) hω hxP]`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]`. Simplify using `only [psi] at hc`.

Rewrite `hc` using `[show α * (x + ω) = α * x + α * ω by ring, hq L (α * ω) (α * x) hαω hx, hq L ω x hω hx0, hsum]`. Take the linear combination `hc`.
-/
lemma eta_rel (hP : IsogenyP) (hd : ZetaHasDeriv) (hq : ZetaQuasi) (L : PeriodPair) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : MulStable L α) (hS : IsKerReps L α S) (ω : ℂ)
    (hω : ω ∈ L.lattice) :
    α * wEta L (α * ω) - ((S.card : ℂ) + 1) * wEta L ω = (∑ P ∈ S, L.weierstrassP P) * ω := by
  have hhalf : L.ω₁ / 2 ∉ L.lattice := by
    intro h
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp h
    have hli := L.indep
    rw [LinearIndependent.pair_iff] at hli
    obtain ⟨h1, h2⟩ := hli ((p : ℝ) - 1 / 2) (q : ℝ) (by
      simp only [Complex.real_smul]
      push_cast
      linear_combination hpq)
    have h3 : (2 : ℝ) * p = 1 := by linarith
    have h2p : (2 * p : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hax : α * (L.ω₁ / 2 / α) = L.ω₁ / 2 := by field_simp
  obtain ⟨x, hx⟩ : ∃ x, α * x ∉ L.lattice := ⟨L.ω₁ / 2 / α, by rw [hax]; exact hhalf⟩
  have hx0 : x ∉ L.lattice := notMem_of_dom hst hx
  have hαω : α * ω ∈ L.lattice := hst ω hω
  have hy : α * (x + ω) ∉ L.lattice := add_dom hαω hx
  have hc := psi_const hP hd L α S hα hst hS hy hx
  have hsum : ∑ P ∈ S, wZeta L (x + ω + P) = ∑ P ∈ S, (wZeta L (x + P) + wEta L ω) := by
    apply Finset.sum_congr rfl
    intro P hPS
    have hxP : x + P ∉ L.lattice := notMem_of_dom hst (add_dom (hS.1 P hPS).1 hx)
    rw [show x + ω + P = x + P + ω by ring, hq L ω (x + P) hω hxP]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  simp only [psi] at hc
  rw [show α * (x + ω) = α * x + α * ω by ring, hq L (α * ω) (α * x) hαω hx, hq L ω x hω hx0,
    hsum] at hc
  linear_combination hc

end S2IsogenyPsi

open S2IsogenyPsi in

/- English proof (translation)
Introduce `L α S hα hst hS`. Establish `hω₁ : L.ω₁ ∈ L.lattice` using `PeriodPair.mem_lattice.mpr ⟨1, 0, by simp⟩`. Establish `hne : L.ω₁ ≠ 0`. Introduce `h0`. Establish `hli` using `L.indep`.

Rewrite `hli` using `[LinearIndependent.pair_iff]`. Establish `h1` using `(hli 1 0 (by rw [h0]; simp)).1`. Conclude with `one_ne_zero h1`. Establish `hrel` using `eta_rel hP hd hq L α S hα hst hS L.ω₁ hω₁`. Rewrite `hrel` using `[he L (α * L.ω₁), he L L.ω₁]`.

Establish `hcard : ((S.card : ℂ) + 1) = (Complex.normSq α : ℂ)`. Establish `h2` using `hc L α S hα hst hS`. Conclude with `h2` after adjusting the coercions. Rewrite `hrel` using `[hcard]`. Rewrite `hrel`, the goal using `[← Complex.mul_conj]`.

Apply `mul_right_cancel₀ hne` to reduce the goal to its premises. Rewrite `hrel` using `[map_mul]`. Take the linear combination `hrel`.
-/
theorem quasiPeriodConstIsogeny_of (hP : IsogenyP) (hd : ZetaHasDeriv) (hq : ZetaQuasi) (he : EtaSplit)
    (hc : KerRepsCard) : QuasiPeriodConstIsogeny := by
  intro L α S hα hst hS
  have hω₁ : L.ω₁ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨1, 0, by simp⟩
  have hne : L.ω₁ ≠ 0 := by
    intro h0
    have hli := L.indep
    rw [LinearIndependent.pair_iff] at hli
    have h1 := (hli 1 0 (by rw [h0]; simp)).1
    exact one_ne_zero h1
  have hrel := eta_rel hP hd hq L α S hα hst hS L.ω₁ hω₁
  rw [he L (α * L.ω₁), he L L.ω₁] at hrel
  have hcard : ((S.card : ℂ) + 1) = (Complex.normSq α : ℂ) := by
    have h2 := hc L α S hα hst hS
    exact_mod_cast h2
  rw [hcard] at hrel
  rw [← Complex.mul_conj] at hrel ⊢
  apply mul_right_cancel₀ hne
  rw [map_mul] at hrel
  linear_combination hrel

/- English proof (translation)
The claim follows from `quasiPeriodConstIsogeny_of isogenyP zetaHasDeriv zetaQuasi etaSplit kerRepsCard`.
-/
theorem quasiPeriodConstIsogeny_thm : QuasiPeriodConstIsogeny := quasiPeriodConstIsogeny_of isogenyP zetaHasDeriv zetaQuasi etaSplit kerRepsCard

/- English proof (translation)
Introduce `L α S hst him hS`. Establish `hα : α ≠ 0`. Introduce `h0`. Apply `him` to reduce the goal to its premises. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Establish `h1` using `h L α S hα hst hS`. Establish `hsub : α - conj α ≠ 0`. Introduce `h0`. Apply `him` to reduce the goal to its premises.

Establish `h2` using `congrArg Complex.im h0`. Simplify using `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h1` using `[← Complex.mul_conj]`. Rewrite using `[eq_div_iff (mul_ne_zero hα hsub)]`.

Take the linear combination `h1`.
-/
theorem cmQuasiPeriodConst_of (h : QuasiPeriodConstIsogeny) : CMQuasiPeriodConst := by
  intro L α S hst him hS
  have hα : α ≠ 0 := by
    intro h0
    apply him
    rw [h0]
    simp
  have h1 := h L α S hα hst hS
  have hsub : α - conj α ≠ 0 := by
    intro h0
    apply him
    have h2 := congrArg Complex.im h0
    simp at h2
    linarith
  rw [← Complex.mul_conj] at h1
  rw [eq_div_iff (mul_ne_zero hα hsub)]
  linear_combination h1

/- English proof (translation)
The claim follows from `cmQuasiPeriodConst_of quasiPeriodConstIsogeny_thm`.
-/
theorem cm_s2 : CMQuasiPeriodConst := cmQuasiPeriodConst_of quasiPeriodConstIsogeny_thm

end Formalism.L2.Th1.F
