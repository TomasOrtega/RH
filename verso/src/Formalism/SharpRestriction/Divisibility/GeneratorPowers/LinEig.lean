import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DegreeOneStatement

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.LinEig

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Jet

variable {S : Type} [CommRing S] {κ : Type}

def tanV (v : κ → S) : Jet S κ (0 + 1) →ₐ[S] DualNumber S :=
  liftJet (MvPolynomial.aeval fun i => v i • (DualNumber.eps : DualNumber S)) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        (MvPolynomial.aeval fun i => v i • (DualNumber.eps : DualNumber S)) (MvPolynomial.X i : MvPolynomial κ S))
        ≤ Ideal.span {(DualNumber.eps : DualNumber S)} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [MvPolynomial.aeval_X, SetLike.mem_coe]
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    refine (Ideal.pow_right_mono h1 _).trans ?_
    rw [Ideal.span_singleton_pow]
    simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tanV_mk (v : κ → S) (P : MvPolynomial κ S) :
    tanV v (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (fun i => v i • (DualNumber.eps : DualNumber S)) P := rfl

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h : ∀ i, MvPolynomial.coeff (Finsupp.single i 1) (MvPolynomial.C a : MvPolynomial κ S) = 0` using `fun i => by`. Rewrite using `[MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm]`. Simplify using `[h]`.

Consider the case `add p q hp hq`. Rewrite using `[map_add, hp, hq, map_add, map_add]`. Simplify using `only [MvPolynomial.coeff_add, add_mul, Finset.sum_add_distrib, add_smul]`. Normalize the expressions using the abelian group laws. Consider the case `mul_X p n hp`.

Rewrite using `[map_mul, hp, MvPolynomial.aeval_X]`. Establish `hc : ∀ i, MvPolynomial.coeff (Finsupp.single i 1) (p * MvPolynomial.X n) = if i = n then MvPolynomial.constantCoeff p else 0`. Introduce `i`. Rewrite using `[MvPolynomial.coeff_mul_X']`. Distinguish the cases in `h : i = n`.

Substitute `h` using the available equality. Rewrite using `[if_pos (by simp), if_pos rfl, tsub_self, MvPolynomial.constantCoeff_eq]`. Rewrite using `[if_neg (by simp [Ne.symm h]), if_neg h]`. Simplify using `only [hc, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, zero_add]`. Apply the tactic sequence `apply TrivSqZeroExt.ext <;> simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]`.
-/
theorem aeval_tan [Fintype κ] [DecidableEq κ] (v : κ → S) (P : MvPolynomial κ S) :
    MvPolynomial.aeval (fun i => v i • (DualNumber.eps : DualNumber S)) P =
      algebraMap S (DualNumber S) (MvPolynomial.constantCoeff P) +
        (∑ i, MvPolynomial.coeff (Finsupp.single i 1) P * v i) • (DualNumber.eps : DualNumber S) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ i, MvPolynomial.coeff (Finsupp.single i 1) (MvPolynomial.C a : MvPolynomial κ S) = 0 := fun i => by
      rw [MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm]
    simp [h]
  | add p q hp hq =>
    rw [map_add, hp, hq, map_add, map_add]
    simp only [MvPolynomial.coeff_add, add_mul, Finset.sum_add_distrib, add_smul]
    abel
  | mul_X p n hp =>
    rw [map_mul, hp, MvPolynomial.aeval_X]
    have hc : ∀ i, MvPolynomial.coeff (Finsupp.single i 1) (p * MvPolynomial.X n) =
        if i = n then MvPolynomial.constantCoeff p else 0 := by
      intro i
      rw [MvPolynomial.coeff_mul_X']
      by_cases h : i = n
      · subst h
        rw [if_pos (by simp), if_pos rfl, tsub_self, MvPolynomial.constantCoeff_eq]
      · rw [if_neg (by simp [Ne.symm h]), if_neg h]
    simp only [hc, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul,
      MvPolynomial.constantCoeff_X, mul_zero, map_zero, zero_add]
    apply TrivSqZeroExt.ext <;> simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

/- English proof (translation)
Establish `hle : orig S κ ≤ RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial κ S →+* S)`. Rewrite using `[orig, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using the standard rewrite rules. Conclude with `hle h`.
-/
theorem const_of_mem_orig {P : MvPolynomial κ S} (h : P ∈ orig S κ) : MvPolynomial.constantCoeff P = 0 := by
  have hle : orig S κ ≤ RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial κ S →+* S) := by
    rw [orig, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp
  exact hle h

/- English proof (translation)
Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Use `show tanV v ((jetMap φ hφ : Jet S κ (0 + 1) →ₐ[S] Jet S κ' (0 + 1)) (Ideal.Quotient.mk _ (MvPolynomial.X i))) = tanV _ (Ideal.Quotient.mk _ (MvPolynomial.X i))`. Establish `e : (jetMap φ hφ : Jet S κ (0 + 1) →ₐ[S] Jet S κ' (0 + 1)) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = Ideal.Quotient.mk _ (φ i)` using `by show Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X i)) = _`.

Rewrite using `[MvPolynomial.aeval_X]`. Rewrite using `[e, tanV_mk, tanV_mk, aeval_tan, MvPolynomial.aeval_X, const_of_mem_orig (hφ i), map_zero, zero_add]`.
-/
theorem tanV_comp_jetMap {κ' : Type} [Fintype κ'] [DecidableEq κ'] (φ : κ → MvPolynomial κ' S)
    (hφ : ∀ i, φ i ∈ orig S κ') (v : κ' → S) :
    (tanV v).comp (jetMap φ hφ : Jet S κ (0 + 1) →ₐ[S] Jet S κ' (0 + 1)) =
      tanV (fun i => ∑ j, MvPolynomial.coeff (Finsupp.single j 1) (φ i) * v j) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show tanV v ((jetMap φ hφ : Jet S κ (0 + 1) →ₐ[S] Jet S κ' (0 + 1)) (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
    tanV _ (Ideal.Quotient.mk _ (MvPolynomial.X i))
  have e : (jetMap φ hφ : Jet S κ (0 + 1) →ₐ[S] Jet S κ' (0 + 1)) (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i) := by
    show Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
  rw [e, tanV_mk, tanV_mk, aeval_tan, MvPolynomial.aeval_X, const_of_mem_orig (hφ i), map_zero, zero_add]

/- English proof (translation)
Establish `hmem : e ∈ degLE m`. Rewrite using `[degLE, Finset.mem_filter, Finset.mem_image]`. Use `⟨⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans he)⟩, Finset.mem_univ _, ?_⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using the standard rewrite rules.

Rewrite `he` using `[Finsupp.degree_apply]`. Conclude with `he`. Rewrite using `[psTrunc, MvPolynomial.coeff_sum, Finset.sum_eq_single e]`. Simplify using `[MvPolynomial.coeff_monomial]`. Introduce `b _ hb`.

Rewrite using `[MvPolynomial.coeff_monomial, if_neg hb]`. Introduce `h`. Conclude with `absurd hmem h`.
-/
theorem coeff_psTrunc' {ιt : Type} [Fintype ιt] [DecidableEq ιt] (m : ℕ) (f : MvPowerSeries ιt S) (e : ιt →₀ ℕ)
    (he : e.degree ≤ m) : MvPolynomial.coeff e (psTrunc m f) = MvPowerSeries.coeff e f := by
  have hmem : e ∈ degLE m := by
    rw [degLE, Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans he)⟩, Finset.mem_univ _, ?_⟩, ?_⟩
    · ext i
      simp
    · rw [Finsupp.degree_apply] at he
      exact he
  rw [psTrunc, MvPolynomial.coeff_sum, Finset.sum_eq_single e]
  · simp [MvPolynomial.coeff_monomial]
  · intro b _ hb
    rw [MvPolynomial.coeff_monomial, if_neg hb]
  · intro h
    exact absurd hmem h

end Jet

section Law

variable {S : Type} [CommRing S] {d : ℕ}

open MvPowerSeries Formalism.FG.SolveVAux in

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LinearTermOfSubstitution.main a ha f t`.
-/
theorem coeff_single_subst' {σ τ : Type} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (a : σ → MvPowerSeries τ S) (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ S) (t : τ) :
    coeff (Finsupp.single t 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single t 1) (a s) :=
  _root_.UpperTheory.Reformulated.B.LinearTermOfSubstitution.main a ha f t

/- English proof (translation)
Establish `hX : ∀ (p q : Fin 1 × Fin d), MvPowerSeries.coeff (Finsupp.single p 1) (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin d) S) = if p = q then 1 else 0`. Introduce `p q`. Rewrite using `[MvPowerSeries.coeff_X]`. Distinguish the cases in `h : p = q`. Simplify using `[h]`.

Rewrite using `[if_neg, if_neg h]`. Introduce `h'`. Conclude with `h (Finsupp.single_left_injective one_ne_zero h')`. Establish `hX2 : ∀ (p q : Fin 2 × Fin d), MvPowerSeries.coeff (Finsupp.single p 1) (MvPowerSeries.X q : MvPowerSeries (Fin 2 × Fin d) S) = if p = q then 1 else 0`. Introduce `p q`.

Rewrite using `[MvPowerSeries.coeff_X]`. Distinguish the cases in `h : p = q`. Simplify using `[h]`. Rewrite using `[if_neg, if_neg h]`. Introduce `h'`.

Conclude with `h (Finsupp.single_left_injective one_ne_zero h')`. Establish `h1 : MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0`. Establish `h` using `congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)) (G.unit i)`. Unfold `Germ.ev at h`. Rewrite using `[coeff_single_subst' _ (by`.

Apply the tactic sequence `rintro ⟨k, l⟩; fin_cases k <;> simp [Germ.pt])] at h`. Rewrite `h` using `[hX]`. Simplify using `only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, zero_add, Germ.pt, hX, Prod.mk.injEq, true_and, mul_ite, _root_.mul_one] at h`. Simplify `h` using `[Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]`. Establish `h0 : MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0`.

Establish `h` using `congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1)) (G.comm i)`. Unfold `Germ.ev at h`. Rewrite using `[coeff_single_subst' _ (by`. Apply the tactic sequence `rintro ⟨k, l⟩; fin_cases k <;> simp [Germ.pt])] at h`. Simplify using `only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Germ.pt, hX2, Prod.mk.injEq, mul_ite, _root_.mul_one, mul_zero] at h`.

Rewrite using `[← h1, ← h]`. Simplify using `[Finset.sum_ite_eq]`. Use `fin_cases k`. Conclude with `h0`. Conclude with `h1`.
-/
theorem law_coeff (G : Germ.FGLaw S d) (i j : Fin d) (k : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single (k, j) 1) (G.F i) = if j = i then 1 else 0 := by
  have hX : ∀ (p q : Fin 1 × Fin d), MvPowerSeries.coeff (Finsupp.single p 1)
      (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin d) S) = if p = q then 1 else 0 := by
    intro p q
    rw [MvPowerSeries.coeff_X]
    by_cases h : p = q
    · simp [h]
    · rw [if_neg, if_neg h]
      intro h'
      exact h (Finsupp.single_left_injective one_ne_zero h')
  have hX2 : ∀ (p q : Fin 2 × Fin d), MvPowerSeries.coeff (Finsupp.single p 1)
      (MvPowerSeries.X q : MvPowerSeries (Fin 2 × Fin d) S) = if p = q then 1 else 0 := by
    intro p q
    rw [MvPowerSeries.coeff_X]
    by_cases h : p = q
    · simp [h]
    · rw [if_neg, if_neg h]
      intro h'
      exact h (Finsupp.single_left_injective one_ne_zero h')

  have h1 : MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0 := by
    have h := congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)) (G.unit i)
    unfold Germ.ev at h
    rw [coeff_single_subst' _ (by
      rintro ⟨k, l⟩; fin_cases k <;> simp [Germ.pt])] at h
    rw [hX] at h
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, zero_add, Germ.pt, hX,
      Prod.mk.injEq, true_and, mul_ite, _root_.mul_one] at h
    simpa [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm] using h
  have h0 : MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0 := by

    have h := congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1)) (G.comm i)
    unfold Germ.ev at h
    rw [coeff_single_subst' _ (by
      rintro ⟨k, l⟩; fin_cases k <;> simp [Germ.pt])] at h
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Germ.pt, hX2, Prod.mk.injEq, mul_ite, _root_.mul_one, mul_zero] at h
    rw [← h1, ← h]
    simp [Finset.sum_ite_eq]
  fin_cases k
  · exact h0
  · exact h1

end Law

section Pts

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {d : ℕ}
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)

def Tv (v : Fin 1 × Fin d → S) : overAt y.x (DualNumber S) ⟶ Xo.univ.t.G :=
  homAt y.x (tanV v : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1

/- English proof (translation)
Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Use `show tm (a • (LinearMap.id : S →ₗ[S] S)) (tanV v (Ideal.Quotient.mk _ (MvPolynomial.X i))) = tanV (a • v) (Ideal.Quotient.mk _ (MvPolynomial.X i))`. Rewrite using `[tanV_mk, tanV_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X]`.

Apply the tactic sequence `apply TrivSqZeroExt.ext <;> simp [tm, mul_comm]`.
-/
theorem tanV_smul {κ : Type} (a : S) (v : κ → S) :
    (tm (a • (LinearMap.id : S →ₗ[S] S))).comp (tanV v : Jet S κ (0 + 1) →ₐ[S] DualNumber S) = tanV (a • v) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show tm (a • (LinearMap.id : S →ₗ[S] S)) (tanV v (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
    tanV (a • v) (Ideal.Quotient.mk _ (MvPolynomial.X i))
  rw [tanV_mk, tanV_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  apply TrivSqZeroExt.ext <;> simp [tm, mul_comm]

/- English proof (translation)
Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Use `show tanV 0 (Ideal.Quotient.mk _ (MvPolynomial.X i)) = Algebra.ofId S (DualNumber S) ((jetAug : Jet S κ (0 + 1) →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X i)))`. Establish `h2 : (jetAug : Jet S κ (0 + 1) →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0` using `by show (MvPolynomial.aeval fun _ => (0 : S)) (MvPolynomial.X i) = _`.

Rewrite using `[MvPolynomial.aeval_X]`. Rewrite using `[tanV_mk, MvPolynomial.aeval_X, h2, map_zero]`. Simplify using the standard rewrite rules.
-/
theorem tanV_zero {κ : Type} :
    (tanV (0 : κ → S) : Jet S κ (0 + 1) →ₐ[S] DualNumber S) =
      (Algebra.ofId S (DualNumber S)).comp (jetAug : Jet S κ (0 + 1) →ₐ[S] S) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show tanV 0 (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
    Algebra.ofId S (DualNumber S) ((jetAug : Jet S κ (0 + 1) →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X i)))
  have h2 : (jetAug : Jet S κ (0 + 1) →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
    show (MvPolynomial.aeval fun _ => (0 : S)) (MvPolynomial.X i) = _
    rw [MvPolynomial.aeval_X]
  rw [tanV_mk, MvPolynomial.aeval_X, h2, map_zero]
  simp

/- English proof (translation)
Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Use `show (MvPolynomial.aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber S) else 0) (MvPolynomial.X i) = tanV (Pi.single ℓ 1) (Ideal.Quotient.mk _ (MvPolynomial.X i))`. Rewrite using `[tanV_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X]`.

Distinguish the cases in `h : i = ℓ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem jetTan_eq {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S) = tanV (Pi.single ℓ 1) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show (MvPolynomial.aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber S) else 0) (MvPolynomial.X i) =
    tanV (Pi.single ℓ 1) (Ideal.Quotient.mk _ (MvPolynomial.X i))
  rw [tanV_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  by_cases h : i = ℓ
  · subst h; simp
  · simp [h]

variable {y x}

/- English proof (translation)
Unfold `Tv smT`. Rewrite using `[← Category.assoc, homAt_comp, tanV_smul]`.
-/
theorem Tv_smul (a : S) (v : Fin 1 × Fin d → S) : Tv y x (a • v) = smT y.x a (Tv y x v) := by
  unfold Tv smT
  rw [← Category.assoc, homAt_comp, tanV_smul]

/- English proof (translation)
Unfold `Tv`. Rewrite using `[tanV_zero, ← homAt_comp, Category.assoc]`. Use `erw [h0]`. Conclude with `MonObj.comp_one _`.
-/
theorem Tv_zero (h0 : homAt y.x (jetAug : Jet S (Fin 1 × Fin d) 1 →ₐ[S] S) ≫ x 1 = 1) : Tv y x 0 = 1 := by
  unfold Tv
  rw [tanV_zero, ← homAt_comp, Category.assoc]
  erw [h0]
  exact MonObj.comp_one _

/- English proof (translation)
Set `ψv : Fin 2 × Fin d → S` to `fun p => if p.1 = 0 then v (0, p.2) else w (0, p.2)`. Establish `hc : ∀ (i : Fin 2), (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S).comp (jetCopy d 1 i : Jet S (Fin 1 × Fin d) 1 →ₐ[S] Jet S (Fin 2 × Fin d) 1) = tanV (fun p : Fin 1 × Fin d => ψv (i, p.2))`. Introduce `i`. Unfold `jetCopy`. Rewrite using `[tanV_comp_jetMap]`.

Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `only [MvPolynomial.coeff_X]`. Rewrite using `[Finset.sum_eq_single (i, p.2)]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[if_neg (fun h => hb (Finsupp.single_left_injective one_ne_zero h).symm), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hL : (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S).comp (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (F.F p.2)) = tanV (v + w)`.

Unfold `jetSubstP`. Rewrite using `[tanV_comp_jetMap]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Establish `hco : ∀ s : Fin 2 × Fin d, MvPolynomial.coeff (Finsupp.single s 1) (psTrunc 1 (F.F p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc 1 (F.F p.2)))) = if s.2 = p.2 then 1 else 0`.

Introduce `s`. Rewrite using `[MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, sub_zero, coeff_psTrunc' 1 _ _ (by simp), law_coeff]`. Simplify using `only [hco, ite_mul, _root_.one_mul, zero_mul, Fintype.sum_prod_type, Fin.sum_univ_two]`. Take `⟨p1, p2⟩` from `p`. Use `fin_cases p1`.

Simplify using `[ψv, Finset.sum_ite_eq']`. Establish `h1 : homAt y.x (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ jpt y d x 1 (0 : Fin 2) = Tv y x v`. Unfold `jpt Tv`. Rewrite using `[← Category.assoc, homAt_comp, hc]`. Use `congr 3`.

Use function extensionality and compare the values at `p`. Take `⟨p1, p2⟩` from `p`. Use `fin_cases p1`. Both sides reduce to the same expression. Establish `h2 : homAt y.x (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ jpt y d x 1 (1 : Fin 2) = Tv y x w`.

Unfold `jpt Tv`. Rewrite using `[← Category.assoc, homAt_comp, hc]`. Use `congr 3`. Use function extensionality and compare the values at `p`. Take `⟨p1, p2⟩` from `p`.

Use `fin_cases p1`. Both sides reduce to the same expression. Rewrite using `[← h1, ← h2, ← MonObj.comp_mul, ← hlaw, ← Category.assoc, homAt_comp, hL]`. Both sides reduce to the same expression.
-/
theorem Tv_add (F : Germ.FGLaw S d)
    (hlaw : homAt y.x (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (F.F p.2)) ≫ x 1 =
      jpt y d x 1 (0 : Fin 2) * jpt y d x 1 (1 : Fin 2)) (v w : Fin 1 × Fin d → S) :
    Tv y x (v + w) = Tv y x v * Tv y x w := by
  classical
  let ψv : Fin 2 × Fin d → S := fun p => if p.1 = 0 then v (0, p.2) else w (0, p.2)
  have hc : ∀ (i : Fin 2), (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S).comp
      (jetCopy d 1 i : Jet S (Fin 1 × Fin d) 1 →ₐ[S] Jet S (Fin 2 × Fin d) 1) =
      tanV (fun p : Fin 1 × Fin d => ψv (i, p.2)) := by
    intro i
    unfold jetCopy
    rw [tanV_comp_jetMap]
    congr 1
    funext p
    simp only [MvPolynomial.coeff_X]
    rw [Finset.sum_eq_single (i, p.2)]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb (Finsupp.single_left_injective one_ne_zero h).symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hL : (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (F.F p.2)) = tanV (v + w) := by
    unfold jetSubstP
    rw [tanV_comp_jetMap]
    congr 1
    funext p
    have hco : ∀ s : Fin 2 × Fin d, MvPolynomial.coeff (Finsupp.single s 1)
        (psTrunc 1 (F.F p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc 1 (F.F p.2)))) =
        if s.2 = p.2 then 1 else 0 := by
      intro s
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm,
        sub_zero, coeff_psTrunc' 1 _ _ (by simp), law_coeff]
    simp only [hco, ite_mul, _root_.one_mul, zero_mul, Fintype.sum_prod_type, Fin.sum_univ_two]
    obtain ⟨p1, p2⟩ := p
    fin_cases p1
    simp [ψv, Finset.sum_ite_eq']
  have h1 : homAt y.x (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ jpt y d x 1 (0 : Fin 2) =
      Tv y x v := by
    unfold jpt Tv
    rw [← Category.assoc, homAt_comp, hc]
    congr 3
    funext p
    obtain ⟨p1, p2⟩ := p
    fin_cases p1
    rfl
  have h2 : homAt y.x (tanV ψv : Jet S (Fin 2 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ jpt y d x 1 (1 : Fin 2) =
      Tv y x w := by
    unfold jpt Tv
    rw [← Category.assoc, homAt_comp, hc]
    congr 3
    funext p
    obtain ⟨p1, p2⟩ := p
    fin_cases p1
    rfl
  rw [← h1, ← h2, ← MonObj.comp_mul, ← hlaw, ← Category.assoc, homAt_comp, hL]
  rfl

end Pts

section Sep

attribute [local instance] Over.cartesianMonoidalCategory

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G : Over X0} [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `s W hs _ _ _ τ hτ`. Rewrite `hs` using `[Finset.card_eq_zero]`.

Substitute `hs` using the available equality. Conclude with `absurd hτ (Finset.notMem_empty τ)`. Consider the case `succ n ih`. Introduce `s W hs hE hT hP τ1 hτ1`. Distinguish the cases in `hone : ∃ τ2 ∈ s, τ2 ≠ τ1`.

Take `⟨τ2, hτ2, hne⟩` from `hone`. Take `⟨a, ha⟩` from `hsep τ1 τ2 hne.symm`. Set `W' : T → (overAt x0 (DualNumber S) ⟶ G)` to `fun τ => smT x0 (χ τ a - χ τ2 a) (W τ)`. Establish `hQ : ∀ τ, W' τ = (W τ ≫ φ a) * smT x0 (-χ τ2 a) (W τ)`. Introduce `τ`.

Rewrite using `[hE, ← smT_add x0 _ (hT τ), ← sub_eq_add_neg]`. Introduce the local definition `Q : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G)`. Use `letI := hφ a`. Use the proof step `(postHom x0 (φ a)) * (smHom x0 (-χ τ2 a))`. Establish `hQ' : ∀ τ, W' τ = Q (W τ)` using `fun τ => hQ τ`.

Establish `hP' : ∏ τ ∈ s, W' τ = 1`. Simplify using `only [hQ']`. Rewrite using `[← map_prod, hP, map_one]`. Establish `hW'2 : W' τ2 = 1` using `by show smT x0 (χ τ2 a - χ τ2 a) (W τ2) = 1`. Rewrite using `[sub_self, hT]`.

Establish `hP'' : ∏ τ ∈ s.erase τ2, W' τ = 1`. Rewrite `hP'` using `[← Finset.mul_prod_erase s W' hτ2, hW'2, _root_.one_mul]`. Conclude with `hP'`. Establish `hE' : ∀ τ a', W' τ ≫ φ a' = smT x0 (χ τ a') (W' τ)`. Introduce `τ a'`.

Use `show smT x0 _ (W τ) ≫ φ a' = smT x0 (χ τ a') (smT x0 _ (W τ))`. Rewrite using `[← smT_post, hE, smT_smT, smT_smT, _root_.mul_comm]`. Establish `hT' : ∀ τ, smT x0 0 (W' τ) = 1`. Introduce `τ`. Use `show smT x0 0 (smT x0 _ (W τ)) = 1`.

Rewrite using `[smT_smT, zero_mul, hT]`. Establish `h1` using `ih (s.erase τ2) W' (by rw [Finset.card_erase_of_mem hτ2, hs]; rfl) hE' hT' hP'' τ1 (Finset.mem_erase.2 ⟨hne.symm, hτ1⟩)`. Take `⟨u, hu⟩` from `ha`. Establish `h2 : smT x0 (↑u⁻¹ : S) (W' τ1) = W τ1` using `by show smT x0 _ (smT x0 _ (W τ1)) = W τ1`. Rewrite using `[smT_smT, ← hu, Units.inv_mul, smT_unit]`.

Rewrite using `[← h2, h1, smT_one']`. Use `push Not at hone`. Establish `hs1 : s = {τ1}`. Use extensionality with `τ`. Prove the components needed by the constructor for the conclusion.

Introduce `hτ`. Conclude with `Finset.mem_singleton.2 (hone τ hτ)`. Introduce `hτ`. Rewrite using `[Finset.mem_singleton.1 hτ]`. Conclude with `hτ1`.

Rewrite `hP` using `[hs1, Finset.prod_singleton]`. Conclude with `hP`.
-/
theorem localization_quotient_separated_dvd {T A : Type} [DecidableEq T] (φ : A → (G ⟶ G)) (hφ : ∀ a, IsMonHom (φ a)) (χ : T → A → S)
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (χ τ a - χ τ' a)) :
    ∀ (n : ℕ) (s : Finset T) (W : T → (overAt x0 (DualNumber S) ⟶ G)), s.card = n →
      (∀ τ a, W τ ≫ φ a = smT x0 (χ τ a) (W τ)) → (∀ τ, smT x0 0 (W τ) = 1) →
      ∏ τ ∈ s, W τ = 1 → ∀ τ ∈ s, W τ = 1 := by
  intro n
  induction n with
  | zero =>
    intro s W hs _ _ _ τ hτ
    rw [Finset.card_eq_zero] at hs
    subst hs
    exact absurd hτ (Finset.notMem_empty τ)
  | succ n ih =>
    intro s W hs hE hT hP τ1 hτ1
    by_cases hone : ∃ τ2 ∈ s, τ2 ≠ τ1
    · obtain ⟨τ2, hτ2, hne⟩ := hone
      obtain ⟨a, ha⟩ := hsep τ1 τ2 hne.symm
      let W' : T → (overAt x0 (DualNumber S) ⟶ G) := fun τ => smT x0 (χ τ a - χ τ2 a) (W τ)
      have hQ : ∀ τ, W' τ = (W τ ≫ φ a) * smT x0 (-χ τ2 a) (W τ) := by
        intro τ
        rw [hE, ← smT_add x0 _ (hT τ), ← sub_eq_add_neg]
      let Q : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G) :=
        letI := hφ a
        (postHom x0 (φ a)) * (smHom x0 (-χ τ2 a))
      have hQ' : ∀ τ, W' τ = Q (W τ) := fun τ => hQ τ
      have hP' : ∏ τ ∈ s, W' τ = 1 := by
        simp only [hQ']
        rw [← map_prod, hP, map_one]
      have hW'2 : W' τ2 = 1 := by
        show smT x0 (χ τ2 a - χ τ2 a) (W τ2) = 1
        rw [sub_self, hT]
      have hP'' : ∏ τ ∈ s.erase τ2, W' τ = 1 := by
        rw [← Finset.mul_prod_erase s W' hτ2, hW'2, _root_.one_mul] at hP'
        exact hP'
      have hE' : ∀ τ a', W' τ ≫ φ a' = smT x0 (χ τ a') (W' τ) := by
        intro τ a'
        show smT x0 _ (W τ) ≫ φ a' = smT x0 (χ τ a') (smT x0 _ (W τ))
        rw [← smT_post, hE, smT_smT, smT_smT, _root_.mul_comm]
      have hT' : ∀ τ, smT x0 0 (W' τ) = 1 := by
        intro τ
        show smT x0 0 (smT x0 _ (W τ)) = 1
        rw [smT_smT, zero_mul, hT]
      have h1 := ih (s.erase τ2) W' (by rw [Finset.card_erase_of_mem hτ2, hs]; rfl) hE' hT' hP'' τ1
        (Finset.mem_erase.2 ⟨hne.symm, hτ1⟩)
      obtain ⟨u, hu⟩ := ha
      have h2 : smT x0 (↑u⁻¹ : S) (W' τ1) = W τ1 := by
        show smT x0 _ (smT x0 _ (W τ1)) = W τ1
        rw [smT_smT, ← hu, Units.inv_mul, smT_unit]
      rw [← h2, h1, smT_one']
    · push Not at hone
      have hs1 : s = {τ1} := by
        ext τ
        constructor
        · intro hτ; exact Finset.mem_singleton.2 (hone τ hτ)
        · intro hτ; rw [Finset.mem_singleton.1 hτ]; exact hτ1
      rw [hs1, Finset.prod_singleton] at hP
      exact hP

/- English proof (translation)
Simplify using `only [combT, Pi.add_apply, smT_add x0 _ (hD _), Finset.prod_mul_distrib]`.
-/
theorem combT_add {m : ℕ} (D : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hD : ∀ j, smT x0 0 (D j) = 1)
    (p q : Fin m → S) : combT x0 D (p + q) = combT x0 D p * combT x0 D q := by
  simp only [combT, Pi.add_apply, smT_add x0 _ (hD _), Finset.prod_mul_distrib]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using combT_zero x0 D hD`. Consider the case `insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, combT_add x0 D hD, ih]`.
-/
theorem combT_sum {m : ℕ} (D : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hD : ∀ j, smT x0 0 (D j) = 1)
    {κ : Type} (s : Finset κ) (f : κ → Fin m → S) : combT x0 D (∑ k ∈ s, f k) = ∏ k ∈ s, combT x0 D (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using combT_zero x0 D hD
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, combT_add x0 D hD, ih]

end Sep

section Pts2

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} {d : ℕ}
variable {x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using h0`. Consider the case `insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, hadd, ih]`.
-/
theorem Tv_sum (h0 : Tv y x 0 = 1) (hadd : ∀ v w, Tv y x (v + w) = Tv y x v * Tv y x w) {κ : Type}
    (s : Finset κ) (f : κ → Fin 1 × Fin d → S) : Tv y x (∑ k ∈ s, f k) = ∏ k ∈ s, Tv y x (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, hadd, ih]

def Dt (y : FrPt Xo c S) (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (j : Fin d) :
    overAt y.x (DualNumber S) ⟶ Xo.univ.t.G :=
  homAt y.x (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1

/- English proof (translation)
Establish `hD : ∀ j, Dt y x j = Tv y x (Pi.single ((0 : Fin 1), j) 1)` using `fun j => by`. Unfold `Dt Tv`. Rewrite using `[jetTan_eq]`. Establish `e : (fun p : Fin 1 × Fin d => w p.2) = ∑ j, w j • (Pi.single ((0 : Fin 1), j) 1 : Fin 1 × Fin d → S)`. Use function extensionality and compare the values at `p`.

Take `⟨p1, p2⟩` from `p`. Use `fin_cases p1`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[e, Tv_sum h0 hadd]`. Unfold `combT`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Tv_smul, hD]`.
-/
theorem combT_Dt (h0 : Tv y x 0 = 1) (hadd : ∀ v w, Tv y x (v + w) = Tv y x v * Tv y x w) (w : Fin d → S) :
    combT y.x (Dt y x) w = Tv y x (fun p => w p.2) := by
  have hD : ∀ j, Dt y x j = Tv y x (Pi.single ((0 : Fin 1), j) 1) := fun j => by
    unfold Dt Tv
    rw [jetTan_eq]
  have e : (fun p : Fin 1 × Fin d => w p.2) = ∑ j, w j • (Pi.single ((0 : Fin 1), j) 1 : Fin 1 × Fin d → S) := by
    funext p
    obtain ⟨p1, p2⟩ := p
    fin_cases p1
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e, Tv_sum h0 hadd]
  unfold combT
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Tv_smul, hD]

/- English proof (translation)
Unfold `Tv`. Rewrite using `[Category.assoc, hact, ← Category.assoc, homAt_comp]`. Unfold `jetSubstP`. Rewrite using `[tanV_comp_jetMap]`. Use `congr 3`.

Use function extensionality and compare the values at `p`. Establish `hco : ∀ s : Fin 1 × Fin d, MvPolynomial.coeff (Finsupp.single s 1) (psTrunc 1 (act p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc 1 (act p.2)))) = MvPowerSeries.coeff (Finsupp.single s 1) (act p.2)`. Introduce `s`. Rewrite using `[MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, sub_zero, coeff_psTrunc' 1 _ _ (by simp)]`. Simplify using `only [hco, Fintype.sum_prod_type, Fin.sum_univ_one]`.

Both sides reduce to the same expression.
-/
theorem Tv_act (a : 𝓞 E) (act : Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (hact : x 1 ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (act p.2)) ≫ x 1)
    (v : Fin 1 × Fin d → S) :
    Tv y x v ≫ Xo.univ.t.act.act a =
      Tv y x (fun p => ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin act p.2 j * v ((0 : Fin 1), j)) := by
  unfold Tv
  rw [Category.assoc, hact, ← Category.assoc, homAt_comp]
  unfold jetSubstP
  rw [tanV_comp_jetMap]
  congr 3
  funext p
  have hco : ∀ s : Fin 1 × Fin d, MvPolynomial.coeff (Finsupp.single s 1)
      (psTrunc 1 (act p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc 1 (act p.2)))) =
      MvPowerSeries.coeff (Finsupp.single s 1) (act p.2) := by
    intro s
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm,
      sub_zero, coeff_psTrunc' 1 _ _ (by simp)]
  simp only [hco, Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

end Pts2

section Main

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `h` to reduce the goal to its premises. Establish `hF : embF c τ = embF c τ'` using `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => hc a)`. Use extensionality with `x`.

Conclude with `congrArg (fun f : E →+* c.F => ((f x : c.F) : ℂ)) hF`.
-/
theorem embK_sep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ τ' : E →+* ℂ) (h : τ ≠ τ') : ∃ a : 𝓞 E, embK c τ a ≠ embK c τ' a := by
  by_contra hc
  push Not at hc
  apply h
  have hF : embF c τ = embF c τ' :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => hc a)
  ext x
  exact congrArg (fun f : E →+* c.F => ((f x : c.F) : ℂ)) hF

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ S _ _ _ y C a ℓ i`. Establish `h0T : Tv y C.x 0 = 1` using `Tv_zero (C.chart.zero 1)`. Establish `haddT : ∀ v w, Tv y C.x (v + w) = Tv y C.x v * Tv y C.x w` using `Tv_add C.B.G (C.chart.law 1)`. Establish `hD : ∀ j, smT y.x 0 (Dt y C.x j) = 1` using `fun j => smT_zero_jetTan y.x ((0 : Fin 1), j) 0 (C.x 1) (C.chart.zero 1)`. Set `Y : Lt1 Dw → (overAt y.x (DualNumber S) ⟶ Xo.univ.t.G)` to `fun ℓ => combT y.x (Dt y C.x) (C.uvec ℓ)`.

Establish `hYl : ∀ ℓ, (Y ℓ).left = y.u ℓ.1 ℓ.2` using `fun ℓ => (isCombAtG_iff Xo.univ.t y.x (Dt y C.x) _ _).1 (C.chart.tan ℓ)`. Establish `hYt : ∀ ℓ, smT y.x 0 (Y ℓ) = 1` using `fun ℓ => combT_tan y.x _ hD _`. Establish `hYe : ∀ ℓ (b : 𝓞 E), Y ℓ ≫ Xo.univ.t.act.act b = smT y.x (algebraMap c.F S (embK c ℓ.1 b)) (Y ℓ)`. Introduce `ℓ b`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[Over.comp_left, smT_left, hYl]`. Conclude with `y.eig ℓ.1 ℓ.2 b`. Set `χ : (E →+* ℂ) → 𝓞 E → S` to `fun τ b => algebraMap c.F S (embK c τ b)`. Establish `hsep : ∀ τ τ', τ ≠ τ' → ∃ b, IsUnit (χ τ b - χ τ' b)`. Introduce `τ τ' hne`.

Take `⟨b, hb⟩` from `embK_sep c τ τ' hne`. Use `⟨b, ?_⟩` and prove the remaining obligations. Use `show IsUnit (algebraMap c.F S (embK c τ b) - algebraMap c.F S (embK c τ' b))`. Rewrite using `[← map_sub]`. Conclude with `(isUnit_iff_ne_zero.2 (sub_ne_zero.2 hb)).map _`.

Establish `inj : ∀ p : Fin C.d → S, combT y.x (Dt y C.x) p = 1 → p = 0`. Introduce `p hp`. Take `⟨b, hb, -⟩` from `C.chart.basis p`. Establish `hpb : p = ∑ ℓ, b ℓ • C.uvec ℓ`. Use function extensionality and compare the values at `j`.

Rewrite using `[← hb j, Finset.sum_apply]`. Simplify using `[smul_eq_mul]`. Set `W : (E →+* ℂ) → (overAt y.x (DualNumber S) ⟶ Xo.univ.t.G)` to `fun τ => combT y.x (fun k : Fin (Dw.mult τ) => Y ⟨τ, k⟩) (fun k => b ⟨τ, k⟩)`. Establish `hprod : ∏ τ ∈ Finset.univ, W τ = 1`. Rewrite using `[← hp, hpb, combT_sum y.x _ hD, Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `show ∏ k, smT y.x (b ⟨τ, k⟩) (Y ⟨τ, k⟩) = _`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smT_combT]`. Both sides reduce to the same expression.

Establish `hWe : ∀ τ (b' : 𝓞 E), W τ ≫ Xo.univ.t.act.act b' = smT y.x (χ τ b') (W τ)`. Introduce `τ b'`. Use `Xo.univ.t.act.hom b'` as an intermediate fact. Conclude with `combT_eig y.x (fun k => Y ⟨τ, k⟩) (Xo.univ.t.act.act b') (χ τ b') (fun k => hYe ⟨τ, k⟩ b') (fun k => b ⟨τ, k⟩)`. Establish `hWt : ∀ τ, smT y.x 0 (W τ) = 1` using `fun τ => combT_tan y.x _ (fun k => hYt _) _`.

Establish `hW1 : ∀ τ, W τ = 1` using `fun τ => localization_quotient_separated_dvd y.x (fun b' => Xo.univ.t.act.act b') (fun b' => Xo.univ.t.act.hom b') χ hsep _ Finset.univ W rfl hWe hWt hprod τ (Finset.mem_univ τ)`. Establish `hb0 : ∀ τ (k : Fin (Dw.mult τ)), b ⟨τ, k⟩ = 0`. Introduce `τ k`. Establish `e : (fun k : Fin (Dw.mult τ) => (Y ⟨τ, k⟩).left) = y.u τ` using `funext fun k => hYl ⟨τ, k⟩`. Establish `h1 : IsCombAt y.x (y.u τ) (fun k => b ⟨τ, k⟩) (W τ).left`.

Use `(isCombAtG_iff Xo.univ.t y.x (fun k : Fin (Dw.mult τ) => Y ⟨τ, k⟩) (fun k => b ⟨τ, k⟩) (W τ).left).2 rfl` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this`. Establish `h2 : IsCombAt y.x (y.u τ) 0 (W τ).left`. Use `(isCombAtG_iff Xo.univ.t y.x (fun k : Fin (Dw.mult τ) => Y ⟨τ, k⟩) 0 (W τ).left).2 (by rw [combT_zero y.x _ (fun k => hYt _), hW1 τ])` as an intermediate fact.

Rewrite `this` using `[e]`. Conclude with `this`. Establish `htan : IsTanAt y.x (W τ).left` using `isTanAtG_of (t := Xo.univ.t) (W τ) (hWt τ)`. Establish `heig : IsEigAt c τ (W τ).left`. Introduce `b'`.

Use `congrArg (fun f => f.left) (hWe τ b')` as an intermediate fact. Simplify `this` using `only [Over.comp_left, smT_left]`. Establish `hu` using `(y.basis τ _ htan heig).unique h1 h2`. Simplify using `using congrFun hu k`. Rewrite using `[hpb]`.

Use `Finset.sum_eq_zero fun ℓ _ => ?_` and prove the remaining obligations. Take `⟨τ, k⟩` from `ℓ`. Rewrite using `[hb0 τ k, zero_smul]`. Establish `e1 : Y ℓ ≫ Xo.univ.t.act.act a = combT y.x (Dt y C.x) (fun i => ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a) i j * C.uvec ℓ j)` using `by show combT y.x (Dt y C.x) (C.uvec ℓ) ≫ _ = _`. Rewrite using `[combT_Dt h0T haddT, Tv_act a (C.B.A.act a) (C.chart.act 1 a), combT_Dt h0T haddT]`.

Establish `e2 : Y ℓ ≫ Xo.univ.t.act.act a = combT y.x (Dt y C.x) (fun i => algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i)`. Rewrite using `[hYe, smT_combT]`. Establish `hz` using `combT_add y.x (Dt y C.x) hD (fun i => ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a) i j * C.uvec ℓ j - algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i) (fun i => algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i)`. Establish `hs : ((fun i => ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a) i j * C.uvec ℓ j - algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i) + fun i => algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i) = fun i => ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a) i j …`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite `hz` using `[hs, ← e1, e2]`. Establish `hd` using `inj _ (mul_eq_right.1 hz.symm)`. Use `congrFun hd i` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`.
-/
theorem linEig_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S]
    [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (a : 𝓞 E) (ℓ : Lt1 Dw) (i : Fin C.d),
    ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a) i j * C.uvec ℓ j = algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C a ℓ i
  classical
  have h0T : Tv y C.x 0 = 1 := Tv_zero (C.chart.zero 1)
  have haddT : ∀ v w, Tv y C.x (v + w) = Tv y C.x v * Tv y C.x w := Tv_add C.B.G (C.chart.law 1)
  have hD : ∀ j, smT y.x 0 (Dt y C.x j) = 1 := fun j =>
    smT_zero_jetTan y.x ((0 : Fin 1), j) 0 (C.x 1) (C.chart.zero 1)
  let Y : Lt1 Dw → (overAt y.x (DualNumber S) ⟶ Xo.univ.t.G) := fun ℓ => combT y.x (Dt y C.x) (C.uvec ℓ)
  have hYl : ∀ ℓ, (Y ℓ).left = y.u ℓ.1 ℓ.2 := fun ℓ =>
    (isCombAtG_iff Xo.univ.t y.x (Dt y C.x) _ _).1 (C.chart.tan ℓ)
  have hYt : ∀ ℓ, smT y.x 0 (Y ℓ) = 1 := fun ℓ => combT_tan y.x _ hD _
  have hYe : ∀ ℓ (b : 𝓞 E), Y ℓ ≫ Xo.univ.t.act.act b = smT y.x (algebraMap c.F S (embK c ℓ.1 b)) (Y ℓ) := by
    intro ℓ b
    apply Over.OverMorphism.ext
    rw [Over.comp_left, smT_left, hYl]
    exact y.eig ℓ.1 ℓ.2 b
  let χ : (E →+* ℂ) → 𝓞 E → S := fun τ b => algebraMap c.F S (embK c τ b)
  have hsep : ∀ τ τ', τ ≠ τ' → ∃ b, IsUnit (χ τ b - χ τ' b) := by
    intro τ τ' hne
    obtain ⟨b, hb⟩ := embK_sep c τ τ' hne
    refine ⟨b, ?_⟩
    show IsUnit (algebraMap c.F S (embK c τ b) - algebraMap c.F S (embK c τ' b))
    rw [← map_sub]
    exact (isUnit_iff_ne_zero.2 (sub_ne_zero.2 hb)).map _

  have inj : ∀ p : Fin C.d → S, combT y.x (Dt y C.x) p = 1 → p = 0 := by
    intro p hp
    obtain ⟨b, hb, -⟩ := C.chart.basis p
    have hpb : p = ∑ ℓ, b ℓ • C.uvec ℓ := by
      funext j
      rw [← hb j, Finset.sum_apply]
      simp [smul_eq_mul]
    let W : (E →+* ℂ) → (overAt y.x (DualNumber S) ⟶ Xo.univ.t.G) := fun τ =>
      combT y.x (fun k : Fin (Dw.mult τ) => Y ⟨τ, k⟩) (fun k => b ⟨τ, k⟩)
    have hprod : ∏ τ ∈ Finset.univ, W τ = 1 := by
      rw [← hp, hpb, combT_sum y.x _ hD, Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun τ _ => ?_
      show ∏ k, smT y.x (b ⟨τ, k⟩) (Y ⟨τ, k⟩) = _
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [smT_combT]
      rfl
    have hWe : ∀ τ (b' : 𝓞 E), W τ ≫ Xo.univ.t.act.act b' = smT y.x (χ τ b') (W τ) := by
      intro τ b'
      have := Xo.univ.t.act.hom b'
      exact combT_eig y.x (fun k => Y ⟨τ, k⟩) (Xo.univ.t.act.act b') (χ τ b') (fun k => hYe ⟨τ, k⟩ b')
        (fun k => b ⟨τ, k⟩)
    have hWt : ∀ τ, smT y.x 0 (W τ) = 1 := fun τ => combT_tan y.x _ (fun k => hYt _) _
    have hW1 : ∀ τ, W τ = 1 := fun τ =>
      localization_quotient_separated_dvd y.x (fun b' => Xo.univ.t.act.act b') (fun b' => Xo.univ.t.act.hom b') χ hsep _ Finset.univ W rfl
        hWe hWt hprod τ (Finset.mem_univ τ)
    have hb0 : ∀ τ (k : Fin (Dw.mult τ)), b ⟨τ, k⟩ = 0 := by
      intro τ k
      have e : (fun k : Fin (Dw.mult τ) => (Y ⟨τ, k⟩).left) = y.u τ := funext fun k => hYl ⟨τ, k⟩
      have h1 : IsCombAt y.x (y.u τ) (fun k => b ⟨τ, k⟩) (W τ).left := by
        have := (isCombAtG_iff Xo.univ.t y.x (fun k : Fin (Dw.mult τ) => Y ⟨τ, k⟩) (fun k => b ⟨τ, k⟩)
          (W τ).left).2 rfl
        rw [e] at this
        exact this
      have h2 : IsCombAt y.x (y.u τ) 0 (W τ).left := by
        have := (isCombAtG_iff Xo.univ.t y.x (fun k : Fin (Dw.mult τ) => Y ⟨τ, k⟩) 0 (W τ).left).2
          (by rw [combT_zero y.x _ (fun k => hYt _), hW1 τ])
        rw [e] at this
        exact this
      have htan : IsTanAt y.x (W τ).left := isTanAtG_of (t := Xo.univ.t) (W τ) (hWt τ)
      have heig : IsEigAt c τ (W τ).left := by
        intro b'
        have := congrArg (fun f => f.left) (hWe τ b')
        simpa only [Over.comp_left, smT_left] using this
      have hu := (y.basis τ _ htan heig).unique h1 h2
      simpa using congrFun hu k
    rw [hpb]
    refine Finset.sum_eq_zero fun ℓ _ => ?_
    obtain ⟨τ, k⟩ := ℓ
    rw [hb0 τ k, zero_smul]

  have e1 : Y ℓ ≫ Xo.univ.t.act.act a =
      combT y.x (Dt y C.x) (fun i => ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a) i j * C.uvec ℓ j) := by
    show combT y.x (Dt y C.x) (C.uvec ℓ) ≫ _ = _
    rw [combT_Dt h0T haddT, Tv_act a (C.B.A.act a) (C.chart.act 1 a), combT_Dt h0T haddT]
  have e2 : Y ℓ ≫ Xo.univ.t.act.act a =
      combT y.x (Dt y C.x) (fun i => algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i) := by
    rw [hYe, smT_combT]
  have hz := combT_add y.x (Dt y C.x) hD
    (fun i => ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a) i j * C.uvec ℓ j -
      algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i)
    (fun i => algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i)
  have hs : ((fun i => ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a) i j * C.uvec ℓ j -
      algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i) +
      fun i => algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i) =
      fun i => ∑ j, ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a) i j * C.uvec ℓ j := by
    funext i
    simp
  rw [hs, ← e1, e2] at hz
  have hd := inj _ (mul_eq_right.1 hz.symm)
  have := congrFun hd i
  simpa [sub_eq_zero] using this

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.LinEig
