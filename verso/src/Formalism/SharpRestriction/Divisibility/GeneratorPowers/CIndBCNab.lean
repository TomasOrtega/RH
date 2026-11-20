import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {d : ℕ}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hasSubst_pts {m n : ℕ} {a : Fin m → Pt S n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem map_ev {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS S m d) :
    map ψ (ev a f) = ev (fun j i => map ψ (a j i)) (map ψ f) := by
  simp only [ev]
  exact MvPowerSeries.map_subst (hasSubst_pts ha) f

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem const_ev {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS S m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have hs := hasSubst_pts ha
  simp only [ev]
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ (0 : Fin m × Fin d →₀ ℕ)]
  · simp
  · intro e he
    obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    simp only [Finsupp.prod, map_prod, map_pow, ha]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (zero_pow hs'), smul_zero]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ S) :
    map ψ (pderiv S i f) = pderiv S' i (map ψ f) := by
  ext n
  simp [MvPowerSeries.coeff_pderiv]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem map_nsmul' {σ : Type} (k : ℕ) (g : MvPowerSeries σ S) :
    map ψ ((k : S) • g) = (k : S') • map ψ g := by
  ext n
  simp

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem map_eval_first_point_zero (g : PS S 2 d) :
    map ψ (ev (n := 1) ![pt S d 0, 0] g) = ev (n := 1) ![pt S' d 0, 0] (map ψ g) := by
  have h0 : ∀ j i, constantCoeff ((![pt S d 0, 0] : Fin 2 → Pt S 1 d) j i) = 0 := by
    intro j i
    fin_cases j <;> simp [pt]
  rw [map_ev ψ _ h0 g]
  congr 1
  funext j i
  fin_cases j <;> simp [pt]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem map_Dof (F : Fin d → PS S 2 d) (v : Fin d → S) (f : PS S 1 d) :
    map ψ (Dof F v f) = Dof (fun j => map ψ (F j)) (fun i => ψ (v i)) (map ψ f) := by
  simp only [Dof, map_sum, map_mul, MvPowerSeries.map_C, map_eval_first_point_zero, map_pderiv]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem map_iter_Dof (F : Fin d → PS S 2 d) (v : Fin d → S) (k : ℕ) (f : PS S 1 d) :
    map ψ ((Dof F v)^[k] f) = (Dof (fun j => map ψ (F j)) (fun i => ψ (v i)))^[k] (map ψ f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, map_Dof]

/- English proof (translation)
Simplify using the standard rewrite rules. Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem map_DmonOf (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S) (e : κ →₀ ℕ)
    (f : PS S 1 d) :
    map ψ (DmonOf F u e f) = DmonOf (fun j => map ψ (F j)) (fun l i => ψ (u l i)) e (map ψ f) := by
  simp only [DmonOf]
  induction (Finset.univ : Finset κ).toList with
  | nil => rfl
  | cons l L ih => simp only [List.foldr_cons, map_iter_Dof, ih]

/- English proof (translation)
Simplify using the standard rewrite rules. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.
-/
theorem map_DpolyOf (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S)
    (P : MvPolynomial κ S) (f : PS S 1 d) :
    map ψ (DpolyOf F u P f) =
      DpolyOf (fun j => map ψ (F j)) (fun l i => ψ (u l i)) (MvPolynomial.map ψ P) (map ψ f) := by
  simp only [DpolyOf, map_sum, map_mul, MvPowerSeries.map_C, map_DmonOf, MvPolynomial.coeff_map]
  symm
  apply Finset.sum_subset (MvPolynomial.support_map_subset ψ P)
  intro e _ he
  have h0 : ψ (P.coeff e) = 0 := by
    simpa [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] using he
  simp [h0]

variable [Algebra ℚ S] [Algebra ℚ S']

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem map_expS {n : ℕ} (g : PS S n d) (hg : constantCoeff g = 0) :
    map ψ (FB.expS S g) = FB.expS S' (map ψ g) := by
  simp only [FB.expS]
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg), PowerSeries.map_exp]

variable {O : Type} [CommRing O] [StarRing O]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hid (R : Type) [CommRing R] : algebraMap R R = RingHom.id R := rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem const_comp1_act (B : FB S d O) (a : O) (i : Fin d) :
    constantCoeff (comp1 (B.actK S a) (pt S (n := 1) d 0) i) = 0 := by
  have h1 : ∀ j l, constantCoeff ((![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) j l) = 0 := by
    intro j l
    fin_cases j
    simp [pt]
  simp only [comp1]
  rw [const_ev _ h1]
  simp [FB.actK, B.A.const]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem const_pair (B : FB S d O) (w0 : O) :
    ∀ j i, constantCoeff ((![pt S d 0, comp1 (B.actK S w0) (pt S d 0)] : Fin 2 → Pt S 1 d) j i) = 0 := by
  intro j i
  fin_cases j
  · simp [pt]
  · simpa using const_comp1_act B w0 i

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem map_hL (B : FB S d O) (B' : FB S' d O) (hA : ∀ a i, B'.A.act a i = map ψ (B.A.act a i))
    (h : PS S 2 d) (w0 : O) : map ψ (B.hL S h w0) = B'.hL S' (map ψ h) w0 := by
  have h1 : ∀ j l, constantCoeff ((![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) j l) = 0 := by
    intro j l
    fin_cases j
    simp [pt]
  simp only [FB.hL]
  rw [map_ev ψ _ (const_pair B w0)]
  congr 1
  funext j i
  fin_cases j
  · simp [pt]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, comp1]
    rw [map_ev ψ _ h1]
    congr 1
    · funext j l
      fin_cases j
      simp [pt]
    · simp [FB.actK, hid, hA]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem const_hL (B : FB S d O) (h : PS S 2 d) (hh : B.IsCanonGauge S h) (w0 : O) :
    constantCoeff (B.hL S h w0) = 0 := by
  simp only [FB.hL]
  rw [const_ev _ (const_pair B w0)]
  have h2 : ∀ j i, constantCoeff ((![0, pt S (n := 1) d 0] : Fin 2 → Pt S 1 d) j i) = 0 := by
    intro j i
    fin_cases j <;> simp [pt]
  have h3 := congrArg constantCoeff hh.ax0
  rwa [const_ev _ h2, map_zero] at h3

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CIndBCNab

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem nabMap_holds : NabMapSt := by
  intro S S' _ _ _ _ ψ d O _ _ B B' hF hA h hh w0 m f κ _ u P
  have hc : constantCoeff ((m : S) • B.hL S h w0) = 0 := by
    simp [MvPowerSeries.smul_eq_C_mul, const_hL B h hh w0]
  have hFK : (fun j => MvPowerSeries.map ψ (B.FK S j)) = B'.FK S' := by
    funext j
    simp [FB.FK, FGLaw.mapF, hF, hid]
  simp only [FB.nabVal]
  rw [← MvPowerSeries.constantCoeff_map, map_DpolyOf, map_mul, map_expS ψ _ hc, map_nsmul',
    map_hL ψ B B' hA, hFK]

end Formalism.MainNotions.ModuliIntegralCharts.H1
