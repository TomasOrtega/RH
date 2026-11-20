import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.MonoVal

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {S : Type} [CommRing S]

open scoped MvPowerSeries.WithPiTopology in
/- English proof (translation)
Use `continuous_pi fun n => ?_` and prove the remaining obligations. Conclude with `((continuous_of_discreteTopology (f := fun x : R => x * ((n i : R) + 1))).comp (continuous_apply (n + Finsupp.single i 1))).congr fun f => (coeff_pderiv f n).symm`.
-/
theorem continuous_pderiv_disc {σ R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (i : σ) : Continuous (fun f : MvPowerSeries σ R => pderiv R i f) := by
  classical
  refine continuous_pi fun n => ?_
  exact ((continuous_of_discreteTopology (f := fun x : R => x * ((n i : R) + 1))).comp
    (continuous_apply (n + Finsupp.single i 1))).congr fun f => (coeff_pderiv f n).symm

open scoped MvPowerSeries.WithPiTopology in

/- English proof (translation)
Establish `hsa : ∀ x y : MvPowerSeries σ S, subst a (x + y) = subst a x + subst a y` using `fun x y => by`. Rewrite using `[← coe_substAlgHom ha, map_add]`. Establish `hm : ∀ x y : MvPowerSeries σ S, subst a (x * y) = subst a x * subst a y` using `fun x y => by`. Rewrite using `[← coe_substAlgHom ha, map_mul]`. Establish `hz : subst a (0 : MvPowerSeries σ S) = 0`.

Rewrite using `[← coe_substAlgHom ha, map_zero]`. Establish `h1 : subst a (1 : MvPowerSeries σ S) = 1`. Rewrite using `[← coe_substAlgHom ha, map_one]`. Establish `hcC : ∀ c : S, subst a (C c : MvPowerSeries σ S) = C c`. Introduce `c`.

Establish `hc : (C c : MvPowerSeries σ S) = c • (1 : MvPowerSeries σ S)`. Rewrite using `[smul_eq_C_mul, mul_one]`. Rewrite using `[hc, ← coe_substAlgHom ha, map_smul, map_one, smul_eq_C_mul, mul_one]`. Establish `hpoly : ∀ p : MvPolynomial σ S, pderiv S t (subst a (p : MvPowerSeries σ S)) = ∑ s, subst a (pderiv S s (p : MvPowerSeries σ S)) * pderiv S t (a s)`. Introduce `p`.

Proceed by induction on `p using MvPolynomial.induction_on`. Use `next c =>`. Simplify using `[MvPolynomial.coe_C, hcC, pderiv_C, hz]`. Use `next p q hp hq =>`. Simplify using `only [MvPolynomial.coe_add, map_add, hsa, add_mul, Finset.sum_add_distrib, hp, hq]`.

Use `next p n hp =>`. Simplify using `only [MvPolynomial.coe_mul, MvPolynomial.coe_X, hm, subst_X ha, Derivation.leibniz, smul_eq_mul, map_add, hsa, pderiv_X, add_mul, Finset.sum_add_distrib, hp, Pi.single_apply, apply_ite (subst a), h1, hz, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', …`. Use `letI : UniformSpace S := ⊥`. Apply the tactic sequence `haveI : DiscreteUniformity S := by first | exact ⟨rfl⟩ | exact inferInstance`. Apply the tactic sequence `haveI : DiscreteTopology S := by first | exact inferInstance | exact ⟨rfl⟩`.

Use `haveI : IsTopologicalRing S := by first`. Consider the case `exact inferInstance`. Consider the case `exact { continuous_add := continuous_of_discreteTopology, continuous_mul := continuous_of_discreteTopology, continuous_neg := continuous_of_discreteTopology }`. Establish `hc1 : Continuous fun f : MvPowerSeries σ S => pderiv S t (subst a f)` using `(continuous_pderiv_disc t).comp (MvPowerSeries.continuous_subst ha)`. Establish `hc2 : Continuous fun f : MvPowerSeries σ S => ∑ s, subst a (pderiv S s f) * pderiv S t (a s)` using `continuous_finset_sum _ fun s _ => ((MvPowerSeries.continuous_subst ha).comp (continuous_pderiv_disc s)).mul continuous_const`.

Establish `heq` using `MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer hc1 hc2 (funext hpoly)`. Conclude with `congrFun heq g`.
-/
theorem pderiv_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (t : τ) (g : MvPowerSeries σ S) :
    pderiv S t (subst a g) = ∑ s, subst a (pderiv S s g) * pderiv S t (a s) := by
  classical
  have hsa : ∀ x y : MvPowerSeries σ S, subst a (x + y) = subst a x + subst a y := fun x y => by
    rw [← coe_substAlgHom ha, map_add]
  have hm : ∀ x y : MvPowerSeries σ S, subst a (x * y) = subst a x * subst a y := fun x y => by
    rw [← coe_substAlgHom ha, map_mul]
  have hz : subst a (0 : MvPowerSeries σ S) = 0 := by
    rw [← coe_substAlgHom ha, map_zero]
  have h1 : subst a (1 : MvPowerSeries σ S) = 1 := by
    rw [← coe_substAlgHom ha, map_one]
  have hcC : ∀ c : S, subst a (C c : MvPowerSeries σ S) = C c := by
    intro c
    have hc : (C c : MvPowerSeries σ S) = c • (1 : MvPowerSeries σ S) := by
      rw [smul_eq_C_mul, mul_one]
    rw [hc, ← coe_substAlgHom ha, map_smul, map_one, smul_eq_C_mul, mul_one]
  have hpoly : ∀ p : MvPolynomial σ S, pderiv S t (subst a (p : MvPowerSeries σ S)) =
      ∑ s, subst a (pderiv S s (p : MvPowerSeries σ S)) * pderiv S t (a s) := by
    intro p
    induction p using MvPolynomial.induction_on
    next c =>
      simp [MvPolynomial.coe_C, hcC, pderiv_C, hz]
    next p q hp hq =>
      simp only [MvPolynomial.coe_add, map_add, hsa, add_mul, Finset.sum_add_distrib, hp, hq]
    next p n hp =>
      simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, hm, subst_X ha, Derivation.leibniz, smul_eq_mul,
        map_add, hsa, pderiv_X, add_mul, Finset.sum_add_distrib, hp, Pi.single_apply, apply_ite (subst a), h1, hz,
        mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.mul_sum, mul_assoc, mul_ite, one_mul]
  letI : UniformSpace S := ⊥
  haveI : DiscreteUniformity S := by first | exact ⟨rfl⟩ | exact inferInstance
  haveI : DiscreteTopology S := by first | exact inferInstance | exact ⟨rfl⟩
  haveI : IsTopologicalRing S := by
    first
    | exact inferInstance
    | exact { continuous_add := continuous_of_discreteTopology, continuous_mul := continuous_of_discreteTopology, continuous_neg := continuous_of_discreteTopology }
  have hc1 : Continuous fun f : MvPowerSeries σ S => pderiv S t (subst a f) :=
    (continuous_pderiv_disc t).comp (MvPowerSeries.continuous_subst ha)
  have hc2 : Continuous fun f : MvPowerSeries σ S => ∑ s, subst a (pderiv S s f) * pderiv S t (a s) :=
    continuous_finset_sum _ fun s _ =>
      ((MvPowerSeries.continuous_subst ha).comp (continuous_pderiv_disc s)).mul continuous_const
  have heq := MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer hc1 hc2 (funext hpoly)
  exact congrFun heq g

/- English proof (translation)
Use `first`. Consider the case `exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)`. Consider the case `exact ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`.
-/
theorem hasSubst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ S} (ha : ∀ s, constantCoeff (a s) = 0) :
    HasSubst a := by
  first
  | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  | exact ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩

/- English proof (translation)
Rewrite using `[constantCoeff_subst (hasSubst0 ha), finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `e he`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, e s ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `he (Finsupp.ext h)`. Establish `hp : constantCoeff (e.prod fun s n => a s ^ n) = 0`. Rewrite using `[Finsupp.prod, map_prod]`. Conclude with `Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [ha s, hs])`.

Simplify using `[hp]`.
-/
theorem const_subst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ S} (ha : ∀ s, constantCoeff (a s) = 0)
    (g : MvPowerSeries σ S) : constantCoeff (subst a g) = constantCoeff g := by
  classical
  rw [constantCoeff_subst (hasSubst0 ha), finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    have hp : constantCoeff (e.prod fun s n => a s ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [ha s, hs])
    simp [hp]

/- English proof (translation)
Use `first`. Consider the case `(rw [← coe_substAlgHom ha, map_sum])`. Consider the case `(induction s using Finset.cons_induction with`. Consider the case `empty => simp [← coe_substAlgHom ha]`. Consider the case `cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, ← ih, ← coe_substAlgHom ha, map_add])`.
-/
theorem subst_sum' {σ τ : Type} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) {ι : Type} (s : Finset ι)
    (g : ι → MvPowerSeries σ S) : subst a (∑ i ∈ s, g i) = ∑ i ∈ s, subst a (g i) := by
  first
  | (rw [← coe_substAlgHom ha, map_sum])
  | (induction s using Finset.cons_induction with
      | empty => simp [← coe_substAlgHom ha]
      | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, ← ih, ← coe_substAlgHom ha, map_add])

variable {N d : ℕ}

/- English proof (translation)
Establish `hc : (C c : MvPowerSeries σ S) = c • (1 : MvPowerSeries σ S)`. Rewrite using `[smul_eq_C_mul, mul_one]`. Rewrite using `[hc, ← coe_substAlgHom ha, map_smul, map_one, smul_eq_C_mul, mul_one]`.
-/
private theorem subst_C_lemma {σ τ : Type} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (c : S) :
    subst a (C c : MvPowerSeries σ S) = C c := by
  have hc : (C c : MvPowerSeries σ S) = c • (1 : MvPowerSeries σ S) := by
    rw [smul_eq_C_mul, mul_one]
  rw [hc, ← coe_substAlgHom ha, map_smul, map_one, smul_eq_C_mul, mul_one]

/- English proof (translation)
Use `first`. Consider the case `(rw [subst_self]; rfl)`. Consider the case `(rw [← map_algebraMap_eq_subst_X]; simp)`.
-/
private theorem subst_X_lemma_2 {σ : Type} (g : MvPowerSeries σ S) :
    subst (X : σ → MvPowerSeries σ S) g = g := by
  first
  | (rw [subst_self]; rfl)
  | (rw [← map_algebraMap_eq_subst_X]; simp)

/- English proof (translation)
Establish `hz : HasSubst (fun _ : σ => (0 : MvPowerSeries τ S))` using `hasSubst0 (fun _ => map_zero _)`. Use extensionality with `e`. Rewrite using `[coeff_subst hz, finsum_eq_single _ 0]`. Apply the tactic sequence `by_cases he : e = 0 <;> simp [coeff_C, coeff_one, he]`. Introduce `n hn`.

Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, n s ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hn (Finsupp.ext h)`. Establish `hp : (n.prod fun _ k => (0 : MvPowerSeries τ S) ^ k) = 0`.

Rewrite using `[Finsupp.prod]`. Conclude with `Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)`. Simplify using `[hp]`.
-/
private theorem subst_zero_lemma_3 {σ τ : Type} [Finite σ] (g : MvPowerSeries σ S) :
    subst (fun _ : σ => (0 : MvPowerSeries τ S)) g = C (constantCoeff g) := by
  classical
  have hz : HasSubst (fun _ : σ => (0 : MvPowerSeries τ S)) := hasSubst0 (fun _ => map_zero _)
  ext e
  rw [coeff_subst hz, finsum_eq_single _ 0]
  · by_cases he : e = 0 <;> simp [coeff_C, coeff_one, he]
  · intro n hn
    obtain ⟨s, hs⟩ : ∃ s, n s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    have hp : (n.prod fun _ k => (0 : MvPowerSeries τ S) ^ k) = 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)
    simp [hp]

/- English proof (translation)
Apply the tactic sequence `have hs : HasSubst (fun p : Fin 2 × Fin N => (![pt S N 0, 0] : Fin 2 → Pt S 1 N) p.1 p.2) := hasSubst0 (by rintro ⟨b, i⟩; fin_cases b <;> simp [pt])`. Establish `h1 : ∀ i j : Fin N, ev (n` using `1) ![pt S N 0, 0] (pderiv S ((1 : Fin 2), i) (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N j)) = if j = i then 1 else 0 := by`. Introduce `i j`. Establish `hp : pderiv S ((1 : Fin 2), i) (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N j) = if j = i then (1 : PS S 2 N) else 0`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using `[ReciprocityTheory.ChartRestriction.G.TB.MV.addF, pderiv_X, Pi.single_apply]`. Simplify using `[ReciprocityTheory.ChartRestriction.G.TB.MV.addF, pderiv_X, Pi.single_apply, h]`. Rewrite using `[hp, ev, ← coe_substAlgHom hs]`. Use `split_ifs`.

Conclude with `map_one _`. Conclude with `map_zero _`. Simplify using `only [Dof, h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']`.
-/
theorem dof_addF (u : Fin N → S) (g : PS S 1 N) :
    Dof (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N) u g = ∑ j, C (u j) * pderiv S ((0 : Fin 1), j) g := by
  classical
  have hs : HasSubst (fun p : Fin 2 × Fin N => (![pt S N 0, 0] : Fin 2 → Pt S 1 N) p.1 p.2) :=
    hasSubst0 (by rintro ⟨b, i⟩; fin_cases b <;> simp [pt])
  have h1 : ∀ i j : Fin N, ev (n := 1) ![pt S N 0, 0]
      (pderiv S ((1 : Fin 2), i) (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N j)) = if j = i then 1 else 0 := by
    intro i j
    have hp : pderiv S ((1 : Fin 2), i) (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N j) =
        if j = i then (1 : PS S 2 N) else 0 := by
      by_cases h : j = i
      · subst h
        simp [ReciprocityTheory.ChartRestriction.G.TB.MV.addF, pderiv_X, Pi.single_apply]
      · simp [ReciprocityTheory.ChartRestriction.G.TB.MV.addF, pderiv_X, Pi.single_apply, h]
    rw [hp, ev, ← coe_substAlgHom hs]
    split_ifs
    · exact map_one _
    · exact map_zero _
  simp only [Dof, h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

section Exp

variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)

abbrev famL : Fin 1 × Fin d → MvPowerSeries (Fin 1 × Fin N) S := fun p => φ p.2

abbrev cpy (b : Fin 2) : Fin 1 × Fin N → MvPowerSeries (Fin 2 × Fin N) S := fun r => X (b, r.2)

abbrev sz : Fin 2 × Fin N → MvPowerSeries (Fin 1 × Fin N) S :=
  fun p => if p.1 = 0 then X ((0 : Fin 1), p.2) else 0

/- English proof (translation)
The claim follows from `hasSubst0 (fun _ => by simp [cpy])`.
-/
theorem hasSubst_cpy (b : Fin 2) : HasSubst (cpy (S := S) (N := N) b) := hasSubst0 (fun _ => by simp [cpy])

/- English proof (translation)
The claim follows from `hasSubst0 (fun p => by by_cases h : p.1 = 0 <;> simp [sz, h])`.
-/
theorem hasSubst_sz : HasSubst (sz (S := S) (N := N)) := hasSubst0 (fun p => by by_cases h : p.1 = 0 <;> simp [sz, h])

/- English proof (translation)
Rewrite using `[subst_comp_subst_apply (hasSubst_cpy b) hasSubst_sz]`. Establish `hf : (fun r : Fin 1 × Fin N => subst (sz (S` using `S) (N := N)) (cpy (S := S) b r)) = fun r => if b = 0 then (X r : MvPowerSeries (Fin 1 × Fin N) S) else 0 := by`. Use function extensionality and compare the values at `r`. Break down `r with ⟨a, i⟩` into its components or cases. Take `rfl : a = 0` from `Subsingleton.elim _ _`.

Use `show subst (sz (S := S) (N := N)) (X (b, i)) = _`. Use `first`. Consider the case `(rw [subst_X hasSubst_sz]; by_cases hb : b = 0 <;> simp [sz, hb])`. Consider the case `rw [subst_X hasSubst_sz]`. Rewrite using `[hf]`.

Distinguish the cases in `hb : b = 0`. Establish `hX : (fun r : Fin 1 × Fin N => if b = 0 then (X r : MvPowerSeries (Fin 1 × Fin N) S) else 0) = X`. Use function extensionality and compare the values at `r`. Simplify using `[hb]`. Rewrite using `[hX, if_pos hb, subst_X_lemma_2]`.

Establish `hZ : (fun r : Fin 1 × Fin N => if b = 0 then (X r : MvPowerSeries (Fin 1 × Fin N) S) else 0) = fun _ => 0`. Use function extensionality and compare the values at `r`. Simplify using `[hb]`. Rewrite using `[hZ, if_neg hb, subst_zero_lemma_3]`.
-/
theorem subst_sz_cpy (b : Fin 2) (g : MvPowerSeries (Fin 1 × Fin N) S) :
    subst (sz (S := S) (N := N)) (subst (cpy (S := S) b) g) = if b = 0 then g else C (constantCoeff g) := by
  classical
  rw [subst_comp_subst_apply (hasSubst_cpy b) hasSubst_sz]
  have hf : (fun r : Fin 1 × Fin N => subst (sz (S := S) (N := N)) (cpy (S := S) b r)) =
      fun r => if b = 0 then (X r : MvPowerSeries (Fin 1 × Fin N) S) else 0 := by
    funext r
    rcases r with ⟨a, i⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    show subst (sz (S := S) (N := N)) (X (b, i)) = _
    first
    | (rw [subst_X hasSubst_sz]; by_cases hb : b = 0 <;> simp [sz, hb])
    | rw [subst_X hasSubst_sz]
  rw [hf]
  by_cases hb : b = 0
  · have hX : (fun r : Fin 1 × Fin N => if b = 0 then (X r : MvPowerSeries (Fin 1 × Fin N) S) else 0) = X := by
      funext r
      simp [hb]
    rw [hX, if_pos hb, subst_X_lemma_2]
  · have hZ : (fun r : Fin 1 × Fin N => if b = 0 then (X r : MvPowerSeries (Fin 1 × Fin N) S) else 0) =
        fun _ => 0 := by
      funext r
      simp [hb]
    rw [hZ, if_neg hb, subst_zero_lemma_3]

/- English proof (translation)
Rewrite using `[pderiv_subst (hasSubst_cpy b), Fintype.sum_prod_type, Fin.sum_univ_one]`. Simplify using `only [cpy, pderiv_X, Pi.single_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hb : b = 1`. Substitute `hb` using the available equality. Simplify using `[Finset.sum_ite_eq, Finset.sum_ite_eq']`.

Simplify using `[hb]`.
-/
theorem pderiv_cpy (b : Fin 2) (q : Fin N) (g : MvPowerSeries (Fin 1 × Fin N) S) :
    pderiv S ((1 : Fin 2), q) (subst (cpy (S := S) b) g) =
      if b = 1 then subst (cpy (S := S) b) (pderiv S ((0 : Fin 1), q) g) else 0 := by
  classical
  rw [pderiv_subst (hasSubst_cpy b), Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [cpy, pderiv_X, Pi.single_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  by_cases hb : b = 1
  · subst hb
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  · simp [hb]

/- English proof (translation)
Establish `hAs : HasSubst (fun p : Fin 2 × Fin d => subst (cpy (S` using `S) p.1) (φ p.2)) := hasSubst0 fun p => constantCoeff_subst_eq_zero (hasSubst_cpy _) (fun r => by simp [cpy]) (h0 p.2)`. Establish `hBs : HasSubst (fun r : Fin 1 × Fin N => (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S))` using `hasSubst0 fun r => by simp`. Establish `hE` using `congrArg (fun G => subst (sz (S := S) (N := N)) (pderiv S ((1 : Fin 2), q) G)) (hhom j)`. Establish `eR : subst (sz (S` using `S) (N := N)) (pderiv S ((1 : Fin 2), q) (subst (fun r : Fin 1 × Fin N => (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) (φ j))) = pderiv S ((0 : Fin 1), q) (φ j) := by`. Rewrite using `[pderiv_subst hBs]`.

Establish `hdB : ∀ r : Fin 1 × Fin N, pderiv S ((1 : Fin 2), q) (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S) = if r = ((0 : Fin 1), q) then 1 else 0`. Introduce and unpack `⟨i, r⟩`. Use `fin_cases i`. Rewrite using `[map_add, pderiv_X_of_ne (by simp [Prod.ext_iff]), zero_add]`. Distinguish the cases in `h : r = q`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[pderiv_X_of_ne (by simp [Prod.ext_iff, h]), if_neg (by simp [Prod.ext_iff, h])]`. Simplify using `only [hdB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[subst_comp_subst_apply hBs hasSubst_sz]`.

Establish `: (fun s : Fin 1 × Fin N => subst (sz (S` using `S) (N := N)) ((X ((0 : Fin 2), s.2) + X ((1 : Fin 2), s.2) : MvPowerSeries (Fin 2 × Fin N) S))) = (X : Fin 1 × Fin N → MvPowerSeries (Fin 1 × Fin N) S) := by`. Use function extensionality and compare the values at `s`. Break down `s with ⟨i, r⟩` into its components or cases. Use `fin_cases i`. Simplify using `[sz, subst_add hasSubst_sz, subst_X hasSubst_sz]`.

Rewrite using `[this, subst_self]`. Both sides reduce to the same expression. Establish `hfam : ∀ g : PS S 2 d, subst (sz (S` using `S) (N := N)) (subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) g) =`. Substitute `(famL φ) (ev (n := 1) ![pt S d 0, 0] g) := by` using the available equality. Introduce `g`.

Apply the tactic sequence `have h2 : HasSubst (fun p : Fin 2 × Fin d => (![pt S d 0, 0] : Fin 2 → Pt S 1 d) p.1 p.2) := hasSubst0 fun p => by rcases p with ⟨b, i⟩; fin_cases b <;> simp [pt]`. Unfold `ev`. Rewrite using `[subst_comp_subst_apply hAs hasSubst_sz, subst_comp_subst_apply h2 (hasSubst0 fun p => h0 p.2)]`. Use `congr 1`. Use function extensionality and compare the values at `p`.

Break down `p with ⟨b, i⟩` into its components or cases. Use `fin_cases b`. Simplify using `[subst_sz_cpy, pt, subst_X (hasSubst0 fun p : Fin 1 × Fin d => h0 p.2)]`. Simplify using `[subst_sz_cpy, h0]`. Rewrite using `[← coe_substAlgHom (hasSubst0 fun p : Fin 1 × Fin d => h0 p.2), map_zero]`.

Rewrite using `[← eR, ← hE, pderiv_subst hAs, subst_sum' hasSubst_sz, Fintype.sum_prod_type, Fin.sum_univ_two]`. Establish `h0s : subst (sz (S` using `S) (N := N)) (0 : MvPowerSeries (Fin 2 × Fin N) S) = 0 := by`. Rewrite using `[← coe_substAlgHom hasSubst_sz, map_zero]`. Simplify using `only [pderiv_cpy, Fin.isValue, zero_ne_one, if_false, if_true, mul_zero, h0s, Finset.sum_const_zero, zero_add]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[subst_mul hasSubst_sz, hfam, subst_sz_cpy, if_neg (by decide)]`. Use `congr 2`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]`. Simplify using `[hlin]`.
-/
theorem key (h0 : ∀ j, constantCoeff (φ j) = 0) (w : Fin N → Fin d → S)
    (hlin : ∀ q j, coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ j) = w q j)
    (hhom : ∀ j, subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) (F j) =
      subst (fun r : Fin 1 × Fin N =>
        (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) (φ j))
    (q : Fin N) (j : Fin d) :
    pderiv S ((0 : Fin 1), q) (φ j) =
      ∑ i, subst (famL φ) (ev (n := 1) ![pt S d 0, 0] (pderiv S ((1 : Fin 2), i) (F j))) * C (w q i) := by
  have hAs : HasSubst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) := hasSubst0 fun p =>
    constantCoeff_subst_eq_zero (hasSubst_cpy _) (fun r => by simp [cpy]) (h0 p.2)
  have hBs : HasSubst (fun r : Fin 1 × Fin N =>
      (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) :=
    hasSubst0 fun r => by simp
  have hE := congrArg (fun G => subst (sz (S := S) (N := N)) (pderiv S ((1 : Fin 2), q) G)) (hhom j)

  have eR : subst (sz (S := S) (N := N)) (pderiv S ((1 : Fin 2), q) (subst (fun r : Fin 1 × Fin N =>
      (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) (φ j))) =
      pderiv S ((0 : Fin 1), q) (φ j) := by
    rw [pderiv_subst hBs]
    have hdB : ∀ r : Fin 1 × Fin N, pderiv S ((1 : Fin 2), q)
        (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S) =
        if r = ((0 : Fin 1), q) then 1 else 0 := by
      rintro ⟨i, r⟩
      fin_cases i
      rw [map_add, pderiv_X_of_ne (by simp [Prod.ext_iff]), zero_add]
      by_cases h : r = q
      · subst h; simp
      · rw [pderiv_X_of_ne (by simp [Prod.ext_iff, h]), if_neg (by simp [Prod.ext_iff, h])]
    simp only [hdB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [subst_comp_subst_apply hBs hasSubst_sz]
    have : (fun s : Fin 1 × Fin N => subst (sz (S := S) (N := N))
        ((X ((0 : Fin 2), s.2) + X ((1 : Fin 2), s.2) : MvPowerSeries (Fin 2 × Fin N) S))) = (X : Fin 1 × Fin N → MvPowerSeries (Fin 1 × Fin N) S) := by
      funext s; rcases s with ⟨i, r⟩; fin_cases i
      simp [sz, subst_add hasSubst_sz, subst_X hasSubst_sz]
    rw [this, subst_self]; rfl

  have hfam : ∀ g : PS S 2 d, subst (sz (S := S) (N := N)) (subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) g) =
      subst (famL φ) (ev (n := 1) ![pt S d 0, 0] g) := by
    intro g
    have h2 : HasSubst (fun p : Fin 2 × Fin d => (![pt S d 0, 0] : Fin 2 → Pt S 1 d) p.1 p.2) :=
      hasSubst0 fun p => by rcases p with ⟨b, i⟩; fin_cases b <;> simp [pt]
    unfold ev
    rw [subst_comp_subst_apply hAs hasSubst_sz, subst_comp_subst_apply h2 (hasSubst0 fun p => h0 p.2)]
    congr 1
    funext p
    rcases p with ⟨b, i⟩
    fin_cases b
    · simp [subst_sz_cpy, pt, subst_X (hasSubst0 fun p : Fin 1 × Fin d => h0 p.2)]
    · simp [subst_sz_cpy, h0]
      rw [← coe_substAlgHom (hasSubst0 fun p : Fin 1 × Fin d => h0 p.2), map_zero]
  rw [← eR, ← hE, pderiv_subst hAs, subst_sum' hasSubst_sz, Fintype.sum_prod_type, Fin.sum_univ_two]
  have h0s : subst (sz (S := S) (N := N)) (0 : MvPowerSeries (Fin 2 × Fin N) S) = 0 := by
    rw [← coe_substAlgHom hasSubst_sz, map_zero]
  simp only [pderiv_cpy, Fin.isValue, zero_ne_one, if_false, if_true, mul_zero, h0s, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [subst_mul hasSubst_sz, hfam, subst_sz_cpy, if_neg (by decide)]
  congr 2
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp [hlin]

end Exp

section Comp

variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
  (h0 : ∀ j, constantCoeff (φ j) = 0) (w : Fin N → Fin d → S)
  (hlin : ∀ q j, coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ j) = w q j)
  (hhom : ∀ j, subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) (F j) =
    subst (fun r : Fin 1 × Fin N =>
      (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin N) S)) (φ j))
include h0 hlin hhom

/- English proof (translation)
Establish `hL : HasSubst (famL φ)` using `hasSubst0 (fun p => h0 p.2)`. Establish `hk : ∀ k : Fin d, pderiv S ((0 : Fin 1), q) (famL φ ((0 : Fin 1), k)) = ∑ i, subst (famL φ) (ev (n` using `1) ![pt S d 0, 0] (pderiv S ((1 : Fin 2), i) (F k))) * C (w q i) := fun k => key F φ h0 w hlin hhom q k`. Rewrite using `[dof_addF, Finset.sum_eq_single q (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]`. Simplify using `only [Pi.single_eq_same, map_one, one_mul]`. Rewrite using `[pderiv_subst hL, Fintype.sum_prod_type, Fin.sum_univ_one]`.

Simplify using `only [hk]`. Rewrite using `[Dof, subst_sum' hL]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← coe_substAlgHom hL, map_mul, map_sum]`. Simplify using `only [map_mul, coe_substAlgHom, subst_C_lemma hL]`.

Rewrite using `[mul_comm]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.
-/
theorem dof_comp (q : Fin N) (g : PS S 1 d) :
    Dof (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N) (Pi.single q 1) (subst (famL φ) g) =
      subst (famL φ) (Dof F (w q) g) := by
  classical
  have hL : HasSubst (famL φ) := hasSubst0 (fun p => h0 p.2)
  have hk : ∀ k : Fin d, pderiv S ((0 : Fin 1), q) (famL φ ((0 : Fin 1), k)) =
      ∑ i, subst (famL φ) (ev (n := 1) ![pt S d 0, 0] (pderiv S ((1 : Fin 2), i) (F k))) * C (w q i) :=
    fun k => key F φ h0 w hlin hhom q k
  rw [dof_addF, Finset.sum_eq_single q (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp only [Pi.single_eq_same, map_one, one_mul]
  rw [pderiv_subst hL, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [hk]
  rw [Dof, subst_sum' hL]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← coe_substAlgHom hL, map_mul, map_sum]
  simp only [map_mul, coe_substAlgHom, subst_C_lemma hL]
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ih, dof_comp F φ h0 w hlin hhom]`.
-/
theorem iter_comp (q : Fin N) (k : ℕ) (g : PS S 1 d) :
    (Dof (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N) (Pi.single q 1))^[k] (subst (famL φ) g) =
      subst (famL φ) ((Dof F (w q))^[k] g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, dof_comp F φ h0 w hlin hhom]

/- English proof (translation)
Unfold `DmonOf`. Generalize the expression as in `(Finset.univ : Finset κ).toList = L`. Proceed by induction on `L with`. Consider the case `nil => rfl`. Consider the case `cons l t ih`.

Simplify using `only [List.foldr_cons]`. Rewrite using `[ih, iter_comp F φ h0 w hlin hhom]`.
-/
theorem dmon_comp {κ : Type} [Fintype κ] (jj : κ → Fin N) (e : κ →₀ ℕ) (g : PS S 1 d) :
    DmonOf (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N) (fun l => Pi.single (jj l) 1) e (subst (famL φ) g) =
      subst (famL φ) (DmonOf F (fun l => w (jj l)) e g) := by
  unfold DmonOf
  generalize (Finset.univ : Finset κ).toList = L
  induction L with
  | nil => rfl
  | cons l t ih =>
    simp only [List.foldr_cons]
    rw [ih, iter_comp F φ h0 w hlin hhom]

/- English proof (translation)
Establish `hL : HasSubst (famL φ)` using `hasSubst0 (fun p => h0 p.2)`. Unfold `DpolyOf`. Rewrite using `[subst_sum' hL]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[dmon_comp F φ h0 w hlin hhom, ← coe_substAlgHom hL, map_mul, coe_substAlgHom, subst_C_lemma hL]`.
-/
theorem dpoly_comp {κ : Type} [Fintype κ] (jj : κ → Fin N) (P : MvPolynomial κ S) (g : PS S 1 d) :
    DpolyOf (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N) (fun l => Pi.single (jj l) 1) P (subst (famL φ) g) =
      subst (famL φ) (DpolyOf F (fun l => w (jj l)) P g) := by
  have hL : HasSubst (famL φ) := hasSubst0 (fun p => h0 p.2)
  unfold DpolyOf
  rw [subst_sum' hL]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dmon_comp F φ h0 w hlin hhom, ← coe_substAlgHom hL, map_mul, coe_substAlgHom, subst_C_lemma hL]

end Comp

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj ExpTieAlg NumberField

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro n`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `n`.

Establish `ih'` using `ih (n + Finsupp.single i 1)`. Establish `e1 : (n + Finsupp.single i 1 : σ →₀ ℕ) i = n i + 1` using `by simp`. Establish `e2 : n + Finsupp.single i 1 + Finsupp.single i k = n + Finsupp.single i (k + 1)`. Rewrite using `[add_assoc, ← Finsupp.single_add, add_comm 1 k]`. Establish `e3 : n i + 1 + k = n i + (k + 1)` using `by omega`.

Rewrite `ih'` using `[e1, e2, e3]`. Rewrite using `[Function.iterate_succ_apply', coeff_pderiv, ← ih', Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem iter_coeff_lemma {S : Type} [CommRing S] {σ : Type} [DecidableEq σ] (i : σ)
    (h : MvPowerSeries σ S) (k : ℕ) : ∀ n : σ →₀ ℕ, ((n i).factorial : S) * coeff n ((pderiv S i)^[k] h) =
      ((n i + k).factorial : S) * coeff (n + Finsupp.single i k) h := by
  induction k with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    have ih' := ih (n + Finsupp.single i 1)
    have e1 : (n + Finsupp.single i 1 : σ →₀ ℕ) i = n i + 1 := by simp
    have e2 : n + Finsupp.single i 1 + Finsupp.single i k = n + Finsupp.single i (k + 1) := by
      rw [add_assoc, ← Finsupp.single_add, add_comm 1 k]
    have e3 : n i + 1 + k = n i + (k + 1) := by omega
    rw [e1, e2, e3] at ih'
    rw [Function.iterate_succ_apply', coeff_pderiv, ← ih', Nat.factorial_succ]
    push_cast
    ring

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro _ n _`. Simplify using the standard rewrite rules. Consider the case `cons l t ih`.

Introduce `hnd n hn`. Rewrite `hnd` using `[List.nodup_cons]`. Establish `hnl : n (v l) = 0` using `hn l (by simp)`. Simplify using `only [List.foldr_cons, List.map_cons, List.prod_cons, List.sum_cons]`. Establish `key1` using `iter_coeff_lemma (v l) (t.foldr (fun l g => (pderiv S (v l))^[α l] g) h) (α l) n`.

Rewrite `key1` using `[hnl, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add]`. Rewrite using `[key1, ih hnd.2 (n + Finsupp.single (v l) (α l)) ?_]`. Rewrite using `[add_assoc]`. Expand and normalize the polynomial expressions, which then agree. Introduce `l' hl'`.

Establish `hne : v l ≠ v l'` using `fun e => hnd.1 (by rw [hv e]; exact hl')`. Simplify using `[hn l' (by simp [hl']), Finsupp.single_apply, hne]`.
-/
private theorem foldr_coeff_lemma_2 {S : Type} [CommRing S] {σ κ : Type} [DecidableEq σ] (v : κ → σ)
    (hv : Function.Injective v) (α : κ → ℕ) (h : MvPowerSeries σ S) : ∀ L : List κ, L.Nodup →
      ∀ n : σ →₀ ℕ, (∀ l ∈ L, n (v l) = 0) →
        coeff n (L.foldr (fun l g => (pderiv S (v l))^[α l] g) h) =
          (L.map fun l => ((α l).factorial : S)).prod *
            coeff (n + (L.map fun l => Finsupp.single (v l) (α l)).sum) h := by
  intro L
  induction L with
  | nil => intro _ n _; simp
  | cons l t ih =>
    intro hnd n hn
    rw [List.nodup_cons] at hnd
    have hnl : n (v l) = 0 := hn l (by simp)
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, List.sum_cons]
    have key1 := iter_coeff_lemma (v l) (t.foldr (fun l g => (pderiv S (v l))^[α l] g) h) (α l) n
    rw [hnl, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add] at key1
    rw [key1, ih hnd.2 (n + Finsupp.single (v l) (α l)) ?_]
    · rw [add_assoc]
      ring
    · intro l' hl'
      have hne : v l ≠ v l' := fun e => hnd.1 (by rw [hv e]; exact hl')
      simp [hn l' (by simp [hl']), Finsupp.single_apply, hne]

/- English proof (translation)
Establish `hD : ∀ q : Fin (dL Dw), (Dof (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S (dL Dw)) (Pi.single q 1) : PS S 1 (dL Dw) → PS S 1 (dL Dw)) = pderiv S ((0 : Fin 1), q)`. Introduce `q`. Use function extensionality and compare the values at `f`. Rewrite using `[dof_addF, Finset.sum_eq_single q (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]`. Simplify using the standard rewrite rules.

Distinguish the cases in `h1 : (1 : S) = 0`. Use `haveI : Subsingleton S := subsingleton_of_zero_eq_one h1.symm`. Conclude with `Subsingleton.elim _ _`. Unfold `DpolyOf DmonOf`. Rewrite using `[MvPolynomial.support_monomial, if_neg h1, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, map_one, one_mul]`.

Simplify using `only [hD]`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, foldr_coeff_lemma_2 (fun l => ((0 : Fin 1), ltIdx Dw l)) ?_ α G _ (Finset.nodup_toList _) 0 (fun _ _ => by simp)]`. Simplify using `only [Finset.prod_toList, Finset.sum_toList, zero_add]`. Rewrite using `[expVal, Finsupp.mapDomain, Finsupp.prod_fintype, Finsupp.sum_fintype]`. Apply the tactic sequence `all_goals simp`.

Introduce `a b hab`. Simplify using `using hab`.
-/
private theorem const_dpoly_lemma_3 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {S : Type} [CommRing S] (α : Lt1 Dw →₀ ℕ) (G : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) :
    constantCoeff (DpolyOf (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S (dL Dw)) (fun l => Pi.single (ltIdx Dw l) 1)
      (MvPolynomial.monomial α 1) G) = expVal G α := by
  classical
  have hD : ∀ q : Fin (dL Dw), (Dof (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S (dL Dw)) (Pi.single q 1) :
      PS S 1 (dL Dw) → PS S 1 (dL Dw)) = pderiv S ((0 : Fin 1), q) := by
    intro q
    funext f
    rw [dof_addF, Finset.sum_eq_single q (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp
  by_cases h1 : (1 : S) = 0
  · haveI : Subsingleton S := subsingleton_of_zero_eq_one h1.symm
    exact Subsingleton.elim _ _
  unfold DpolyOf DmonOf
  rw [MvPolynomial.support_monomial, if_neg h1, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl,
    map_one, one_mul]
  simp only [hD]
  rw [← coeff_zero_eq_constantCoeff_apply, foldr_coeff_lemma_2 (fun l => ((0 : Fin 1), ltIdx Dw l)) ?_ α G _
    (Finset.nodup_toList _) 0 (fun _ _ => by simp)]
  · simp only [Finset.prod_toList, Finset.sum_toList, zero_add]
    rw [expVal, Finsupp.mapDomain, Finsupp.prod_fintype, Finsupp.sum_fintype]
    all_goals simp
  · intro a b hab
    simpa using hab

/- English proof (translation)
Establish `h0` using `hφ.const`. Establish `hlin : ∀ (q : Fin (dL Dw)) (j : Fin d), coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ j) = uvec ((ltIdx Dw).symm q) j`. Introduce `q j`. Simplify using `using hφ.lin ((ltIdx Dw).symm q) j`. Establish `hd` using `dpoly_comp F φ h0 (fun q j => uvec ((ltIdx Dw).symm q) j) hlin hφ.hom (fun l => ltIdx Dw l) (MvPolynomial.monomial α 1) g`.

Simplify using `only [Equiv.symm_apply_apply] at hd`. Rewrite using `[← const_subst0 (a := famL φ) (fun p => h0 p.2) (DpolyOf F uvec (MvPolynomial.monomial α 1) g), ← hd]`. Conclude with `const_dpoly_lemma_3 α (subst (famL φ) g)`.
-/
theorem tie_alg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {S : Type} [CommRing S]
    {d : ℕ} (F : Fin d → PS S 2 d) (uvec : Lt1 Dw → Fin d → S)
    (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : IsExpOf F uvec φ) (α : Lt1 Dw →₀ ℕ) (g : PS S 1 d) :
    constantCoeff (DpolyOf F uvec (MvPolynomial.monomial α 1) g) = expVal (compL φ g) α := by
  classical
  have h0 := hφ.const
  have hlin : ∀ (q : Fin (dL Dw)) (j : Fin d), coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ j) =
      uvec ((ltIdx Dw).symm q) j := by
    intro q j
    simpa using hφ.lin ((ltIdx Dw).symm q) j
  have hd := dpoly_comp F φ h0 (fun q j => uvec ((ltIdx Dw).symm q) j) hlin hφ.hom (fun l => ltIdx Dw l)
    (MvPolynomial.monomial α 1) g
  simp only [Equiv.symm_apply_apply] at hd
  rw [← const_subst0 (a := famL φ) (fun p => h0 p.2) (DpolyOf F uvec (MvPolynomial.monomial α 1) g), ← hd]
  exact const_dpoly_lemma_3 α (subst (famL φ) g)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(simp only [FB.nabVal, FB.FK]; rfl)`.
-/
theorem nabVal_eq_const {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    (B : FB S d O) (h : PS S 2 d) (w0 : O) (k : ℕ) (f : PS S 1 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S)
    (P : MvPolynomial κ S) :
    B.nabVal S h w0 k f u P = constantCoeff (DpolyOf B.G.F u P (f * FB.expS S ((k : S) • B.hL S h w0))) := by
  first
  | rfl
  | (simp only [FB.nabVal, FB.FK]; rfl)

end Formalism.MainNotions.ModuliIntegralCharts.H1
