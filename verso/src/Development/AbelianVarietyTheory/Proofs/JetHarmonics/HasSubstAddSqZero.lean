import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ContinuousPderivDisc

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.Jets

/- English proof (translation)
Apply `hasSubst_of_constantCoeff_nilpotent` to reduce the goal to its premises. Introduce `s`. Rewrite using `[map_add, map_mul]`. Establish `h1 : IsNilpotent (constantCoeff e)` using `⟨2, by rw [pow_two, ← map_mul, he, map_zero]⟩`. Conclude with `(Commute.all _ _).isNilpotent_add (ha s) ((Commute.all _ _).isNilpotent_mul_right h1)`.
-/
theorem hasSubst_add_sqZero {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha : ∀ s, IsNilpotent (constantCoeff (a s))) : HasSubst (fun s => a s + e * b s) := by
  apply hasSubst_of_constantCoeff_nilpotent
  intro s
  rw [map_add, map_mul]
  have h1 : IsNilpotent (constantCoeff e) := ⟨2, by rw [pow_two, ← map_mul, he, map_zero]⟩
  exact (Commute.all _ _).isNilpotent_add (ha s) ((Commute.all _ _).isNilpotent_mul_right h1)

open scoped MvPowerSeries.WithPiTopology in

/- English proof (translation)
Use `letI : UniformSpace S := ⊥`. Use `haveI : DiscreteUniformity S := ⟨rfl⟩`. Establish `ha : HasSubst a` using `hasSubst_of_constantCoeff_nilpotent ha0`. Establish `hb : HasSubst (fun s => a s + e * b s)` using `hasSubst_add_sqZero a b e he ha0`. Establish `hca : Continuous (subst a : MvPowerSeries σ S → MvPowerSeries τ S)` using `continuous_subst ha`.

Establish `hcb : Continuous (subst (fun s => a s + e * b s) : MvPowerSeries σ S → MvPowerSeries τ S)` using `continuous_subst hb`. Establish `hs0 : subst a (0 : MvPowerSeries σ S) = 0` using `by rw [← coe_substAlgHom ha, map_zero]`. Establish `hs1 : subst a (1 : MvPowerSeries σ S) = 1` using `by rw [← coe_substAlgHom ha, map_one]`. Set `D2 : MvPowerSeries σ S → MvPowerSeries τ S` to `fun g =>`. Substitute `a g + e * ∑ s, b s * subst a (pderiv S s g)` using the available equality.

Establish `c2 : Continuous D2` using `hca.add (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul (hca.comp (continuous_pderiv_disc _))))`. Establish `hpoly : ∀ p : MvPolynomial σ S,`. Substitute `(fun s => a s + e * b s) (p : MvPowerSeries σ S) = D2 (p : MvPowerSeries σ S) := by` using the available equality. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`.

Consider the case `C r => simp [D2, subst_C, hs0]`. Consider the case `add p q hp hq`. Simplify using `only [D2, MvPolynomial.coe_add, subst_add ha, subst_add hb, map_add] at hp hq ⊢`. Rewrite using `[hp, hq]`. Simplify using `only [mul_add, Finset.sum_add_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p s hp`. Simplify using `only [D2, MvPolynomial.coe_mul, MvPolynomial.coe_X] at hp ⊢`. Rewrite using `[subst_mul ha, subst_X ha, subst_mul hb, subst_X hb, hp]`. Establish `hX : ∀ i : σ, pderiv S i (X s : MvPowerSeries σ S) = if i = s then 1 else 0`.

Introduce `i`. Distinguish the cases in `h : i = s`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, pderiv_X_of_ne]`.

Introduce `h'`. Conclude with `h h'.symm`. Establish `hterm : ∀ i : σ, b i * subst a (pderiv S i ((p : MvPowerSeries σ S) * X s)) = (if i = s then b i * subst a (p : MvPowerSeries σ S) else 0) + a s * (b i * subst a (pderiv S i (p : MvPowerSeries σ S)))`. Introduce `i`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, hX i, subst_add ha, subst_mul ha, subst_mul ha, subst_X ha]`.

Use `split_ifs with h`. Rewrite using `[hs1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs0]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← Finset.mul_sum]`. Take the linear combination `(b s * ∑ i, b i * subst a (pderiv S i (p : MvPowerSeries σ S))) * he`. Use `(MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries).equalizer hcb c2 (funext hpoly)` as an intermediate fact. Conclude with `congrFun this g`.
-/
theorem subst_add_sqZero {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha0 : ∀ s, IsNilpotent (constantCoeff (a s))) (g : MvPowerSeries σ S) :
    subst (fun s => a s + e * b s) g = subst a g + e * ∑ s, b s * subst a (pderiv S s g) := by
  classical
  letI : UniformSpace S := ⊥
  haveI : DiscreteUniformity S := ⟨rfl⟩
  have ha : HasSubst a := hasSubst_of_constantCoeff_nilpotent ha0
  have hb : HasSubst (fun s => a s + e * b s) := hasSubst_add_sqZero a b e he ha0
  have hca : Continuous (subst a : MvPowerSeries σ S → MvPowerSeries τ S) := continuous_subst ha
  have hcb : Continuous (subst (fun s => a s + e * b s) :
      MvPowerSeries σ S → MvPowerSeries τ S) := continuous_subst hb
  have hs0 : subst a (0 : MvPowerSeries σ S) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have hs1 : subst a (1 : MvPowerSeries σ S) = 1 := by rw [← coe_substAlgHom ha, map_one]
  let D2 : MvPowerSeries σ S → MvPowerSeries τ S := fun g =>
    subst a g + e * ∑ s, b s * subst a (pderiv S s g)
  have c2 : Continuous D2 :=
    hca.add (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (hca.comp (continuous_pderiv_disc _))))
  have hpoly : ∀ p : MvPolynomial σ S,
      subst (fun s => a s + e * b s) (p : MvPowerSeries σ S) = D2 (p : MvPowerSeries σ S) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => simp [D2, subst_C, hs0]
    | add p q hp hq =>
      simp only [D2, MvPolynomial.coe_add, subst_add ha, subst_add hb, map_add] at hp hq ⊢
      rw [hp, hq]
      simp only [mul_add, Finset.sum_add_distrib]
      ring
    | mul_X p s hp =>
      simp only [D2, MvPolynomial.coe_mul, MvPolynomial.coe_X] at hp ⊢
      rw [subst_mul ha, subst_X ha, subst_mul hb, subst_X hb, hp]
      have hX : ∀ i : σ, pderiv S i (X s : MvPowerSeries σ S) = if i = s then 1 else 0 := by
        intro i
        by_cases h : i = s
        · subst h; simp
        · rw [if_neg h, pderiv_X_of_ne]
          intro h'
          exact h h'.symm
      have hterm : ∀ i : σ, b i * subst a (pderiv S i ((p : MvPowerSeries σ S) * X s)) =
          (if i = s then b i * subst a (p : MvPowerSeries σ S) else 0) +
            a s * (b i * subst a (pderiv S i (p : MvPowerSeries σ S))) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hX i, subst_add ha, subst_mul ha,
          subst_mul ha, subst_X ha]
        split_ifs with h
        · rw [hs1]; ring
        · rw [hs0]; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), ← Finset.mul_sum]
      linear_combination (b s * ∑ i, b i * subst a (pderiv S i (p : MvPowerSeries σ S))) * he
  have := (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries).equalizer hcb c2 (funext hpoly)
  exact congrFun this g

/- English proof (translation)
Use extensionality with `n`. Simplify using `[coeff_pderiv]`.
-/
theorem map_pderiv' {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (i : σ)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by
  classical
  ext n
  simp [coeff_pderiv]

/- English proof (translation)
Introduce and unpack `⟨j, i⟩`. Apply the tactic sequence `fin_cases j <;> simp [pt]`.
-/
theorem hasSubst_pt_zero (R : Type) [CommRing R] (d : ℕ) :
    ∀ p : Fin 2 × Fin d,
      constantCoeff ((![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) = 0 := by
  rintro ⟨j, i⟩
  fin_cases j <;> simp [pt]

/- English proof (translation)
Establish `hb : HasSubst (fun p : Fin 2 × Fin d => (![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2)` using `hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d)`. Establish `ha : HasSubst (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2)` using `hasSubst_of_constantCoeff_zero (by`. Introduce and unpack `⟨j, i⟩`. Apply the tactic sequence `fin_cases j <;> simp [pt])`. Rewrite using `[← G.comm i, ← G.unit i]`.

Unfold `ev`. Rewrite using `[subst_comp_subst_apply ha hb]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Take `⟨j, l⟩` from `p`.

Use `fin_cases j`. Conclude with `subst_X hb ((1 : Fin 2), l)`. Conclude with `subst_X hb ((0 : Fin 2), l)`.
-/
theorem law_right_unit {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (i : Fin d) :
    ev (n := 1) ![pt R d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS R 1 d) := by
  have hb : HasSubst (fun p : Fin 2 × Fin d => (![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d)
  have ha : HasSubst
      (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j <;> simp [pt])
  rw [← G.comm i, ← G.unit i]
  unfold ev
  rw [subst_comp_subst_apply ha hb]
  congr 1
  funext p
  obtain ⟨j, l⟩ := p
  fin_cases j
  · exact subst_X hb ((1 : Fin 2), l)
  · exact subst_X hb ((0 : Fin 2), l)

/- English proof (translation)
Unfold `ev`. Rewrite using `[MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d))]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Take `⟨j, l⟩` from `p`.

Apply the tactic sequence `fin_cases j <;> simp [pt]`.
-/
theorem map_ev_pt_zero {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (φ : R →+* S)
    (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := 1) ![pt R d 0, 0] g) =
      ev (n := 1) ![pt S d 0, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d))]
  congr 1
  funext p
  obtain ⟨j, l⟩ := p
  fin_cases j <;> simp [pt]

/- English proof (translation)
Rewrite using `[← map_mul, DualNumber.eps_mul_eps, map_zero]`.
-/
theorem C_eps_mul_self (R : Type) [CommRing R] (τ : Type) :
    (C (DualNumber.eps : DualNumber R) : MvPowerSeries τ (DualNumber R)) * C DualNumber.eps = 0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

/- English proof (translation)
Establish `h` using `subst_add_sqZero (fun p : Fin 2 × Fin d => (![pt (DualNumber R) d 0, 0] : Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2) (fun p : Fin 2 × Fin d => (![0, fun i => C (algebraMap R (DualNumber R) (v i))] : Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2) (C DualNumber.eps) (C_eps_mul_self R _) (fun …`. Establish `h1` using `map_ev_pt_zero (algebraMap R (DualNumber R)) (G.F j)`. Rewrite `h1` using `[law_right_unit, map_X]`. Rewrite using `[h1, map_sum]`. Simplify using `only [map_mul, map_C, map_ev_pt_zero, map_pderiv']`.

Rewrite `h` using `[Fintype.sum_prod_type, Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at h`. Use `Eq.trans ?_ h` and prove the remaining obligations. Unfold `addOf ev FGLaw.mapF`. Use `congr 1`.

Use function extensionality and compare the values at `p`. Take `⟨l, i⟩` from `p`. Use `fin_cases l`. Simplify using the standard rewrite rules. Simplify using `only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply, zero_add]`.

Rewrite using `[← map_mul]`. Use `congr 1`. Apply the tactic sequence `ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem addOf_eps {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (v : Fin d → R) (j : Fin d) :
    addOf (n := 1) (G.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
        (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R)) j =
      X ((0 : Fin 1), j) + C (DualNumber.eps : DualNumber R) *
        MvPowerSeries.map (algebraMap R (DualNumber R))
          (∑ i : Fin d, C (v i) *
            ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F j))) := by
  have h := subst_add_sqZero
    (fun p : Fin 2 × Fin d => (![pt (DualNumber R) d 0, 0] : Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2)
    (fun p : Fin 2 × Fin d => (![0, fun i => C (algebraMap R (DualNumber R) (v i))] :
      Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2)
    (C DualNumber.eps) (C_eps_mul_self R _)
    (fun p => by rw [hasSubst_pt_zero]; exact IsNilpotent.zero)
    (MvPowerSeries.map (algebraMap R (DualNumber R)) (G.F j))
  have h1 := map_ev_pt_zero (algebraMap R (DualNumber R)) (G.F j)
  rw [law_right_unit, map_X] at h1
  rw [h1, map_sum]
  simp only [map_mul, map_C, map_ev_pt_zero, map_pderiv']
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add] at h
  refine Eq.trans ?_ h
  unfold addOf ev FGLaw.mapF
  congr 1
  funext p
  obtain ⟨l, i⟩ := p
  fin_cases l
  · simp
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
      zero_add]
    rw [← map_mul]
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Introduce `R _ d G v f`. Establish `h` using `subst_add_sqZero (X : Fin 1 × Fin d → PS (DualNumber R) 1 d) (fun p : Fin 1 × Fin d => MvPowerSeries.map (algebraMap R (DualNumber R)) (∑ i : Fin d, C (v i) * ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F p.2)))) (C DualNumber.eps) (C_eps_mul_self R _) (fun p => by r …`. Rewrite `h` using `[subst_self, Fintype.sum_prod_type, Fin.sum_univ_one]`. Unfold `Dof`. Rewrite using `[map_sum]`.

Simplify using `only [map_mul (MvPowerSeries.map (algebraMap R (DualNumber R))) (∑ i : Fin d, _) (pderiv R _ f), map_pderiv' (algebraMap R (DualNumber R)) _ f]`. Use `Eq.trans ?_ h` and prove the remaining obligations. Unfold `ev`. Use `congr 1`. Use function extensionality and compare the values at `p`.

Take `⟨l, j⟩` from `p`. Take `rfl : l = 0` from `Subsingleton.elim _ _`. Conclude with `addOf_eps G v j`.
-/
theorem ev_addOf_eps :
    ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (v : Fin d → R) (f : PS R 1 d),
      ev (n := 1) ![addOf (G.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
          (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R))]
        (MvPowerSeries.map (algebraMap R (DualNumber R)) f) =
      MvPowerSeries.map (algebraMap R (DualNumber R)) f +
        C (DualNumber.eps : DualNumber R) *
          MvPowerSeries.map (algebraMap R (DualNumber R)) (Dof G.F v f) := by
  intro R _ d G v f
  have h := subst_add_sqZero
    (X : Fin 1 × Fin d → PS (DualNumber R) 1 d)
    (fun p : Fin 1 × Fin d => MvPowerSeries.map (algebraMap R (DualNumber R))
          (∑ i : Fin d, C (v i) *
            ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F p.2))))
    (C DualNumber.eps) (C_eps_mul_self R _)
    (fun p => by rw [constantCoeff_X]; exact IsNilpotent.zero)
    (MvPowerSeries.map (algebraMap R (DualNumber R)) f)
  rw [subst_self, Fintype.sum_prod_type, Fin.sum_univ_one] at h
  unfold Dof
  rw [map_sum]
  simp only [map_mul (MvPowerSeries.map (algebraMap R (DualNumber R)))
    (∑ i : Fin d, _) (pderiv R _ f), map_pderiv' (algebraMap R (DualNumber R)) _ f]
  refine Eq.trans ?_ h
  unfold ev
  congr 1
  funext p
  obtain ⟨l, j⟩ := p
  obtain rfl : l = 0 := Subsingleton.elim _ _
  exact addOf_eps G v j

end GlobalTheory.Jets
