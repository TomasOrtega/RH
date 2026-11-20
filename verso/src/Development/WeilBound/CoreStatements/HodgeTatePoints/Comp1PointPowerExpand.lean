import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet

noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

section Alg

variable {k : Type} [CommRing k]

/- English proof (translation)
Establish `: (jetAug : Jet k κ m →ₐ[k] k) (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (fun _ => (0 : k)) P` using `rfl`. Rewrite using `[this, MvPolynomial.aeval_zero']`. Both sides reduce to the same expression.
-/
theorem aug_mk {κ : Type} (m : ℕ) (P : MvPolynomial κ k) :
    (jetAug : Jet k κ m →ₐ[k] k) (Ideal.Quotient.mk _ P) = MvPolynomial.constantCoeff P := by
  have : (jetAug : Jet k κ m →ₐ[k] k) (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (fun _ => (0 : k)) P := rfl
  rw [this, MvPolynomial.aeval_zero']
  rfl

/- English proof (translation)
Rewrite using `[jetSubstP, jetMap_mk, MvPolynomial.aeval_X]`.
-/
theorem substP_X {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' k) (i : κ) :
    jetSubstP m φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) := by
  rw [jetSubstP, jetMap_mk, MvPolynomial.aeval_X]

/- English proof (translation)
Use extensionality with `e`. Establish `hR : MvPolynomial.coeff e (∑ j, MvPolynomial.C (MvPowerSeries.coeff (Finsupp.single j 1) V) * MvPolynomial.X j ^ p : MvPolynomial σ k) = ∑ j, if Finsupp.single j p = e then MvPowerSeries.coeff (Finsupp.single j 1) V else 0`. Rewrite using `[MvPolynomial.coeff_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hR]`. Distinguish the cases in `hs : ∃ j, Finsupp.single j p = e`. Take `⟨j, rfl⟩` from `hs`. Rewrite using `[GermFun.coeff_psTrunc _ _ _ (by simp), Finset.sum_eq_single j, if_pos rfl]`.

Establish `: Finsupp.single j p = p • Finsupp.single j 1` using `by simp`. Rewrite using `[this, MvPowerSeries.coeff_expand_smul]`. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `hb ((Finsupp.single_left_inj hp).1 h)`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_zero fun j _ => if_neg fun h => hs ⟨j, h⟩]`. Distinguish the cases in `hd : e.degree ≤ p`. Rewrite using `[GermFun.coeff_psTrunc _ _ _ hd]`.

Distinguish the cases in `hdv : ∀ i, p ∣ e i`. Use `choose c hc using hdv`. Set `e' : σ →₀ ℕ` to `Finsupp.equivFunOnFinite.symm c`. Establish `he : e = p • e'` using `by ext i; simp [e', hc]`. Establish `hdeg : e'.degree ≤ 1`.

Rewrite `hd` using `[he, map_nsmul, smul_eq_mul]`. Assume the negation of the conclusion as `hh`. Establish `: p * 2 ≤ p * e'.degree` using `Nat.mul_le_mul_left _ (by omega)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[he, MvPowerSeries.coeff_expand_smul]`.

Break down `Nat.le_one_iff_eq_zero_or_eq_one.1 hdeg with h0 | h1` into its components or cases. Rewrite using `[(Finsupp.degree_eq_zero_iff _).1 h0]`. Simplify using `using hV`. It suffices to derive a contradiction. Establish `h1' : e' ∈ {d : σ →₀ ℕ | d.degree = 1}` using `h1`.

Rewrite `h1'` using `[← Finsupp.range_single_one]`. Take `⟨j, hj⟩` from `h1'`. Conclude with `hs ⟨j, by rw [he, ← hj]; simp⟩`. Use `push Not at hdv`. Take `⟨i, hi⟩` from `hdv`.

Conclude with `MvPowerSeries.coeff_expand_of_not_dvd _ _ _ hi`. Rewrite using `[psTrunc, MvPolynomial.coeff_sum]`. Use `Finset.sum_eq_zero fun b hb => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_monomial, if_neg]`. Introduce and unpack `rfl`.

Apply `hd` to reduce the goal to its premises. Use `(Finset.mem_filter.1 hb).2` as an intermediate fact. Simplify `this` using `[Finsupp.degree_apply, Finsupp.sum]`.
-/
theorem psTrunc_expand {σ : Type} [Fintype σ] [DecidableEq σ] (p : ℕ) (hp : p ≠ 0) (V : MvPowerSeries σ k)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    psTrunc p (MvPowerSeries.expand p hp V) =
      ∑ j, MvPolynomial.C (MvPowerSeries.coeff (Finsupp.single j 1) V) * MvPolynomial.X j ^ p := by
  ext e
  have hR : MvPolynomial.coeff e
      (∑ j, MvPolynomial.C (MvPowerSeries.coeff (Finsupp.single j 1) V) * MvPolynomial.X j ^ p : MvPolynomial σ k) =
      ∑ j, if Finsupp.single j p = e then MvPowerSeries.coeff (Finsupp.single j 1) V else 0 := by
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
    split_ifs <;> simp
  rw [hR]
  by_cases hs : ∃ j, Finsupp.single j p = e
  · obtain ⟨j, rfl⟩ := hs
    rw [GermFun.coeff_psTrunc _ _ _ (by simp), Finset.sum_eq_single j, if_pos rfl]
    · have : Finsupp.single j p = p • Finsupp.single j 1 := by simp
      rw [this, MvPowerSeries.coeff_expand_smul]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb ((Finsupp.single_left_inj hp).1 h)
    · simp
  · rw [Finset.sum_eq_zero fun j _ => if_neg fun h => hs ⟨j, h⟩]
    by_cases hd : e.degree ≤ p
    · rw [GermFun.coeff_psTrunc _ _ _ hd]
      by_cases hdv : ∀ i, p ∣ e i
      · choose c hc using hdv
        let e' : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm c
        have he : e = p • e' := by ext i; simp [e', hc]
        have hdeg : e'.degree ≤ 1 := by
          rw [he, map_nsmul, smul_eq_mul] at hd
          by_contra hh
          have : p * 2 ≤ p * e'.degree := Nat.mul_le_mul_left _ (by omega)
          omega
        rw [he, MvPowerSeries.coeff_expand_smul]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hdeg with h0 | h1
        · rw [(Finsupp.degree_eq_zero_iff _).1 h0]
          simpa using hV
        · exfalso
          have h1' : e' ∈ {d : σ →₀ ℕ | d.degree = 1} := h1
          rw [← Finsupp.range_single_one] at h1'
          obtain ⟨j, hj⟩ := h1'
          exact hs ⟨j, by rw [he, ← hj]; simp⟩
      · push Not at hdv
        obtain ⟨i, hi⟩ := hdv
        exact MvPowerSeries.coeff_expand_of_not_dvd _ _ _ hi
    · rw [psTrunc, MvPolynomial.coeff_sum]
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [MvPolynomial.coeff_monomial, if_neg]
      rintro rfl
      apply hd
      have := (Finset.mem_filter.1 hb).2
      simpa [Finsupp.degree_apply, Finsupp.sum] using this

/- English proof (translation)
Establish `: (fun q : Fin 1 × Fin d => (![ptPow k d p (0 : Fin 1)] : Fin 1 → Germ.Pt k 1 d) q.1 q.2) = fun q => MvPowerSeries.X q ^ p`. Use function extensionality and compare the values at `⟨a, b⟩`. Take `rfl : a = 0` from `Subsingleton.elim _ _`. Both sides reduce to the same expression. Rewrite using `[Germ.comp1, Germ.ev, this, MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]`.
-/
theorem comp1_point_power_expand {d : ℕ} (p : ℕ) (hp : p ≠ 0) (V : Germ.Pt k 1 d) (i : Fin d) :
    Germ.comp1 V (ptPow k d p (0 : Fin 1)) i = MvPowerSeries.expand p hp (V i) := by
  have : (fun q : Fin 1 × Fin d => (![ptPow k d p (0 : Fin 1)] : Fin 1 → Germ.Pt k 1 d) q.1 q.2) =
      fun q => MvPowerSeries.X q ^ p := by
    funext ⟨a, b⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  rw [Germ.comp1, Germ.ev, this, MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]

def trTo (k : Type) [CommRing k] (κ : Type) {m n : ℕ} (h : n ≤ m) : Jet k κ m →ₐ[k] Jet k κ n :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trTo_mk {κ : Type} {m n : ℕ} (h : n ≤ m) (P : MvPolynomial κ k) :
    trTo k κ h (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ P := rfl

/- English proof (translation)
Rewrite `h` using `[aug_mk]`. Simplify `sub_const_mem_orig P` using `[h]`.
-/
theorem mem_orig_of_aug {κ : Type} {m : ℕ} {P : MvPolynomial κ k}
    (h : (jetAug : Jet k κ m →ₐ[k] k) (Ideal.Quotient.mk _ P) = 0) : P ∈ orig k κ := by
  rw [aug_mk] at h
  simpa [h] using sub_const_mem_orig P

/- English proof (translation)
Use `choose P hP using fun q => Ideal.Quotient.mk_surjective (χ (Ideal.Quotient.mk _ (MvPolynomial.X q)))`. Establish `hm : ∀ q, P q ∈ orig k κ'` using `fun q => mem_orig_of_aug (by rw [hP]; exact hχ q)`. Use `⟨jetMap P hm, fun q => ?_, jet_hom_ext fun q => ?_⟩` and prove the remaining obligations. Rewrite using `[jetMap_mk, MvPolynomial.aeval_X, aug_mk, ← aug_mk m, hP]`. Conclude with `hχ q`.

Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, trTo_mk, jetMap_mk, MvPolynomial.aeval_X, ← hP, trTo_mk]`.
-/
theorem exists_low {κ κ' : Type} {m n : ℕ} (h : n ≤ m) (χ : Jet k κ m →ₐ[k] Jet k κ' m)
    (hχ : ∀ q, (jetAug : Jet k κ' m →ₐ[k] k) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) :
    ∃ χ' : Jet k κ n →ₐ[k] Jet k κ' n,
      (∀ q, (jetAug : Jet k κ' n →ₐ[k] k) (χ' (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧
      χ'.comp (trTo k κ h) = (trTo k κ' h).comp χ := by
  choose P hP using fun q => Ideal.Quotient.mk_surjective (χ (Ideal.Quotient.mk _ (MvPolynomial.X q)))
  have hm : ∀ q, P q ∈ orig k κ' := fun q => mem_orig_of_aug (by rw [hP]; exact hχ q)
  refine ⟨jetMap P hm, fun q => ?_, jet_hom_ext fun q => ?_⟩
  · rw [jetMap_mk, MvPolynomial.aeval_X, aug_mk, ← aug_mk m, hP]
    exact hχ q
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, trTo_mk, jetMap_mk, MvPolynomial.aeval_X, ← hP, trTo_mk]

/- English proof (translation)
Use `haveI : CharP (MvPolynomial κ k) p := inferInstance`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite `h` using `[trTo_mk, trTo_mk, Ideal.Quotient.eq]`. Rewrite using `[← map_pow, ← map_pow, Ideal.Quotient.eq, ← sub_pow_char]`.

Use `Ideal.pow_mem_pow h p` as an intermediate fact. Rewrite `this` using `[← pow_mul]`. Conclude with `Ideal.pow_le_pow_right (by omega) this`.
-/
theorem pow_eq_of_first {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) {κ : Type}
    (a b : Jet k κ p) (h : trTo k κ hp a = trTo k κ hp b) : a ^ p = b ^ p := by
  haveI : CharP (MvPolynomial κ k) p := inferInstance
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [trTo_mk, trTo_mk, Ideal.Quotient.eq] at h
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq, ← sub_pow_char]
  have := Ideal.pow_mem_pow h p
  rw [← pow_mul] at this
  exact Ideal.pow_le_pow_right (by omega) this

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `t.act.add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Simplify using `using this`.

Consider the case `succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, pow_succ]`.
-/
theorem act_nat (t : SAB H X0) (n : ℕ) : t.act.act (n : 𝓞 E) = (𝟙 t.G) ^ n := by
  induction n with
  | zero =>
    have := t.act.add 0 0
    rw [add_zero] at this
    simpa using this
  | succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, pow_succ]

/- English proof (translation)
Rewrite using `[act_nat, MonObj.comp_pow, Category.comp_id]`.
-/
theorem pow_eq_act {T : Over X0} (y : T ⟶ t.G) (n : ℕ) : y ^ n = y ≫ t.act.act (n : 𝓞 E) := by
  rw [act_nat, MonObj.comp_pow, Category.comp_id]

variable {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d : ℕ} (g : GermAt t x d)

/- English proof (translation)
Proceed by induction on `m, h using Nat.le_induction with`. Consider the case `base`. Establish `: trTo S (Fin 1 × Fin d) (le_refl n) = AlgHom.id S _` using `jet_hom_ext fun _ => rfl`. Rewrite using `[this, homAt_id, Category.id_comp]`. Consider the case `succ m h ih`.

Establish `: trTo S (Fin 1 × Fin d) (h.trans (Nat.le_succ m)) = (trTo S (Fin 1 × Fin d) h).comp jetTrunc` using `jet_hom_ext fun _ => rfl`. Rewrite using `[this, ← homAt_comp, Category.assoc, g.chart.trunc, ih]`.
-/
theorem x_trTo {m n : ℕ} (h : n ≤ m) : homAt x (trTo S (Fin 1 × Fin d) h) ≫ g.x m = g.x n := by
  induction m, h using Nat.le_induction with
  | base =>
    have : trTo S (Fin 1 × Fin d) (le_refl n) = AlgHom.id S _ := jet_hom_ext fun _ => rfl
    rw [this, homAt_id, Category.id_comp]
  | succ m h ih =>
    have : trTo S (Fin 1 × Fin d) (h.trans (Nat.le_succ m)) = (trTo S (Fin 1 × Fin d) h).comp jetTrunc :=
      jet_hom_ext fun _ => rfl
    rw [this, ← homAt_comp, Category.assoc, g.chart.trunc, ih]

/- English proof (translation)
Establish `: χ = (Algebra.ofId S A).comp jetAug` using `jet_hom_ext fun q => by`. Rewrite using `[hχ, AlgHom.comp_apply, aug_mk]`. Simplify using the standard rewrite rules. Rewrite using `[this, ← homAt_comp, Category.assoc, g.chart.zero, MonObj.comp_one]`.
-/
theorem x_zero {A : Type} [CommRing A] [Algebra S A] {m : ℕ} (χ : Jet S (Fin 1 × Fin d) m →ₐ[S] A)
    (hχ : ∀ q, χ (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0) : homAt x χ ≫ g.x m = 1 := by
  have : χ = (Algebra.ofId S A).comp jetAug := jet_hom_ext fun q => by
    rw [hχ, AlgHom.comp_apply, aug_mk]
    simp
  rw [this, ← homAt_comp, Category.assoc, g.chart.zero, MonObj.comp_one]

/- English proof (translation)
Take `⟨V, hc, hV, hl⟩` from `hV`. Use `⟨χ.comp (jetSubstP p fun q : Fin 1 × Fin d => psTrunc p (g.B.A.act (p : 𝓞 E) q.2)), ?_, fun q => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_eq_act, Category.assoc, g.chart.act, ← Category.assoc, homAt_comp]`. Rewrite using `[AlgHom.comp_apply, substP_X, hV, comp1_point_power_expand p hp, psTrunc_expand p hp _ (hc _), ← hl]`. Simplify using `only [map_sum, map_mul, map_pow, MvPolynomial.constantCoeff_X, zero_pow hp, mul_zero, Finset.sum_const_zero, map_zero, sub_zero, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `χ.commutes _`.
-/
theorem pow_coord {A : Type} [CommRing A] [Algebra S A] (p : ℕ) (hp : p ≠ 0)
    (hV : ∃ V : Germ.Pt S 1 d, (∀ i, MvPowerSeries.constantCoeff (V i) = 0) ∧
      g.B.A.act (p : 𝓞 E) = Germ.comp1 V (ptPow S d p 0) ∧ lin V 1 = hw g.B p)
    (χ : Jet S (Fin 1 × Fin d) p →ₐ[S] A) :
    ∃ ψ : Jet S (Fin 1 × Fin d) p →ₐ[S] A, (homAt x χ ≫ g.x p) ^ p = homAt x ψ ≫ g.x p ∧
      ∀ q, ψ (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
        ∑ j, algebraMap S A (hw g.B p q.2 j) * χ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) ^ p := by
  obtain ⟨V, hc, hV, hl⟩ := hV
  refine ⟨χ.comp (jetSubstP p fun q : Fin 1 × Fin d => psTrunc p (g.B.A.act (p : 𝓞 E) q.2)), ?_, fun q => ?_⟩
  · rw [pow_eq_act, Category.assoc, g.chart.act, ← Category.assoc, homAt_comp]
  · rw [AlgHom.comp_apply, substP_X, hV, comp1_point_power_expand p hp, psTrunc_expand p hp _ (hc _), ← hl]
    simp only [map_sum, map_mul, map_pow, MvPolynomial.constantCoeff_X, zero_pow hp, mul_zero,
      Finset.sum_const_zero, map_zero, sub_zero, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact χ.commutes _

end Geo

end PositivityTheory.HtPt.Ce
