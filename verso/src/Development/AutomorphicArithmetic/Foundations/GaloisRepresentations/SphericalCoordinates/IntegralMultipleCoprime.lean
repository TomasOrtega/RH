import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private def unitBall (p : ℕ) [Fact p.Prime] : Subring (PadicAlgCl p) where
  carrier := {y | ‖y‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (PadicAlgCl.isNonarchimedean p a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by simp

/- English proof (translation)
Introduce `hd`. Establish `hnum : ¬ (p : ℤ) ∣ q.num`. Introduce `hn`. Establish `h1 : p ∣ q.num.natAbs` using `Int.natCast_dvd.mp hn`. Establish `h2` using `Nat.dvd_gcd h1 hd`.

Rewrite `h2` using `[Nat.Coprime.gcd_eq_one q.reduced]`. Conclude with `hp.out.one_lt.ne' (Nat.dvd_one.mp h2)`. Establish `hn1 : ‖(q.num : ℚ_[p])‖ = 1` using `le_antisymm (Padic.norm_int_le_one _) (not_lt.mp fun hlt => hnum (Padic.norm_intCast_lt_one_iff.mp hlt))`. Establish `hd1 : ‖(q.den : ℚ_[p])‖ < 1` using `Padic.norm_natCast_lt_one_iff.mpr hd`. Establish `heq : (q : ℚ_[p]) * q.den = q.num` using `by exact_mod_cast Rat.mul_den_eq_num q`.

Establish `hn` using `congrArg norm heq`. Rewrite `hn` using `[norm_mul, hn1]`. Use polynomial arithmetic with `[norm_nonneg (q.den : ℚ_[p]), norm_nonneg (q : ℚ_[p])]`.
-/
private theorem den_of_norm {p : ℕ} [hp : Fact p.Prime] (q : ℚ) (h : ‖(q : ℚ_[p])‖ ≤ 1) :
    ¬ p ∣ q.den := by
  intro hd
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have h2 := Nat.dvd_gcd h1 hd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  have hn1 : ‖(q.num : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _)
      (not_lt.mp fun hlt => hnum (Padic.norm_intCast_lt_one_iff.mp hlt))
  have hd1 : ‖(q.den : ℚ_[p])‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hd
  have heq : (q : ℚ_[p]) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have hn := congrArg norm heq
  rw [norm_mul, hn1] at hn
  nlinarith [norm_nonneg (q.den : ℚ_[p]), norm_nonneg (q : ℚ_[p])]

/- English proof (translation)
Establish `hx : IsIntegral ℚ x` using `Algebra.IsIntegral.isIntegral x`. Use `set P := (minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl p)) with hP`. Establish `hPm : P.Monic` using `(minpoly.monic hx).map _`. Establish `hroot : ∀ r ∈ P.roots, ‖r‖ ≤ 1`. Introduce `r hr`.

Establish `hr' : r ∈ (minpoly ℚ x).rootSet (PadicAlgCl p)`. Rewrite using `[Polynomial.mem_rootSet]`. Use `⟨minpoly.ne_zero hx, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]`. Conclude with `(Polynomial.mem_roots hPm.ne_zero).mp hr`.

Rewrite `hr'` using `[← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly]`. Take `⟨ψ, rfl⟩` from `hr'`. Conclude with `h ψ.toRingHom`. Establish `hprod : (P.roots.map fun a => Polynomial.X - Polynomial.C a).prod = P` using `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm IsAlgClosed.card_roots_eq_natDegree`. Establish `hlift : P ∈ Polynomial.lifts (unitBall p).subtype`.

Rewrite using `[← hprod]`. Use `Subsemiring.multiset_prod_mem _ _ ?_` and prove the remaining obligations. Introduce `f hf`. Take `⟨a, ha, rfl⟩` from `Multiset.mem_map.mp hf`. Conclude with `⟨Polynomial.X - Polynomial.C ⟨a, hroot a ha⟩, by simp⟩`.

Take `⟨y, hy⟩` from `(Polynomial.lifts_iff_coeff_lifts P).mp hlift i`. Establish `hn : ‖P.coeff i‖ ≤ 1`. Rewrite using `[← hy]`. Conclude with `y.2`. Rewrite `hn` using `[hP, Polynomial.coeff_map]`.

Apply `den_of_norm` to reduce the goal to its premises. Establish `hc : algebraMap ℚ (PadicAlgCl p) ((minpoly ℚ x).coeff i) = algebraMap ℚ_[p] (PadicAlgCl p) (((minpoly ℚ x).coeff i : ℚ) : ℚ_[p])`. Simplify using `only [eq_ratCast, map_ratCast]`. Rewrite `hn` using `[hc]`. Conclude with `(PadicAlgCl.norm_extends p _).symm.trans_le hn`.
-/
private theorem coeff_den {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (x : F)
    (h : ∀ τ : F →+* PadicAlgCl p, ‖τ x‖ ≤ 1) (i : ℕ) : ¬ p ∣ ((minpoly ℚ x).coeff i).den := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  set P := (minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl p)) with hP
  have hPm : P.Monic := (minpoly.monic hx).map _
  have hroot : ∀ r ∈ P.roots, ‖r‖ ≤ 1 := by
    intro r hr
    have hr' : r ∈ (minpoly ℚ x).rootSet (PadicAlgCl p) := by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero hx, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.mem_roots hPm.ne_zero).mp hr
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hr'
    obtain ⟨ψ, rfl⟩ := hr'
    exact h ψ.toRingHom
  have hprod : (P.roots.map fun a => Polynomial.X - Polynomial.C a).prod = P :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm IsAlgClosed.card_roots_eq_natDegree
  have hlift : P ∈ Polynomial.lifts (unitBall p).subtype := by
    rw [← hprod]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro f hf
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hf
    exact ⟨Polynomial.X - Polynomial.C ⟨a, hroot a ha⟩, by simp⟩
  obtain ⟨y, hy⟩ := (Polynomial.lifts_iff_coeff_lifts P).mp hlift i
  have hn : ‖P.coeff i‖ ≤ 1 := by
    rw [← hy]
    exact y.2
  rw [hP, Polynomial.coeff_map] at hn
  apply den_of_norm
  have hc : algebraMap ℚ (PadicAlgCl p) ((minpoly ℚ x).coeff i)
      = algebraMap ℚ_[p] (PadicAlgCl p) (((minpoly ℚ x).coeff i : ℚ) : ℚ_[p]) := by
    simp only [eq_ratCast, map_ratCast]
  rw [hc] at hn
  exact (PadicAlgCl.norm_extends p _).symm.trans_le hn

/- English proof (translation)
Establish `hx : IsIntegral ℚ x` using `Algebra.IsIntegral.isIntegral x`. Use `set P := minpoly ℚ x with hP`. Use `set M : ℕ := ∏ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).den with hM`. Establish `hMcop : M.Coprime p` using `Nat.Coprime.prod_left fun i _ => ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr (h i)).symm`. Establish `hQ : P.scaleRoots (M : ℚ) ∈ Polynomial.lifts (Int.castRingHom ℚ)`.

Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `i`. Rewrite using `[Polynomial.coeff_scaleRoots]`. Distinguish the cases in `hi : i ≤ P.natDegree`. Break down `hi.lt_or_eq with hlt | heq` into its components or cases.

Take `⟨k, hk⟩ : (P.coeff i).den ∣ M` from `Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))`. Establish `hc : P.coeff i * M = (P.coeff i).num * k`. Rewrite using `[hk]`. Use `push_cast`. Rewrite using `[← _root_.mul_assoc, Rat.mul_den_eq_num]`.

Establish `hpow : (M : ℚ) ^ (P.natDegree - i) = M * M ^ (P.natDegree - i - 1)`. Rewrite using `[← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Use `⟨(P.coeff i).num * k * M ^ (P.natDegree - i - 1), ?_⟩` and prove the remaining obligations.

Rewrite using `[hpow, ← _root_.mul_assoc, hc]`. Simplify using the standard rewrite rules. Substitute `heq` using the available equality. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.sub_self, pow_zero, _root_.mul_one, map_one]`.

Conclude with `(minpoly.monic hx).leadingCoeff.symm`. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `[Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]`. Establish `hmon : (P.scaleRoots (M : ℚ)).Monic` using `(Polynomial.monic_scaleRoots_iff _).mpr (minpoly.monic hx)`. Take `⟨Q, hQmap, -, hQm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hQ hmon`.

Establish `hint : IsIntegral ℤ ((M : F) * x)`. Use `⟨Q, hQm, ?_⟩` and prove the remaining obligations. Establish `h0` using `Polynomial.scaleRoots_aeval_eq_zero (r := (M : ℚ)) (minpoly.aeval ℚ x)`. Establish `hcast : Int.castRingHom ℚ = algebraMap ℤ ℚ` using `Subsingleton.elim _ _`. Rewrite `h0` using `[← hP, ← hQmap, hcast, Polynomial.aeval_map_algebraMap, map_natCast]`.

Rewrite using `[← Polynomial.aeval_def]`. Conclude with `h0`. Conclude with `⟨M, ⟨(M : F) * x, hint⟩, hMcop, rfl⟩`.
-/
private theorem integral_multiple_coprime {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (x : F)
    (h : ∀ i, ¬ p ∣ ((minpoly ℚ x).coeff i).den) :
    ∃ (m : ℕ) (c : 𝓞 F), m.Coprime p ∧ (c : F) = m * x := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  set P := minpoly ℚ x with hP
  set M : ℕ := ∏ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).den with hM
  have hMcop : M.Coprime p :=
    Nat.Coprime.prod_left fun i _ =>
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr (h i)).symm
  have hQ : P.scaleRoots (M : ℚ) ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    by_cases hi : i ≤ P.natDegree
    · rcases hi.lt_or_eq with hlt | heq
      · obtain ⟨k, hk⟩ : (P.coeff i).den ∣ M :=
          Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
        have hc : P.coeff i * M = (P.coeff i).num * k := by
          rw [hk]
          push_cast
          rw [← _root_.mul_assoc, Rat.mul_den_eq_num]
        have hpow : (M : ℚ) ^ (P.natDegree - i) = M * M ^ (P.natDegree - i - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        refine ⟨(P.coeff i).num * k * M ^ (P.natDegree - i - 1), ?_⟩
        rw [hpow, ← _root_.mul_assoc, hc]
        simp
      · subst heq
        refine ⟨1, ?_⟩
        rw [Nat.sub_self, pow_zero, _root_.mul_one, map_one]
        exact (minpoly.monic hx).leadingCoeff.symm
    · refine ⟨0, ?_⟩
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
  have hmon : (P.scaleRoots (M : ℚ)).Monic := (Polynomial.monic_scaleRoots_iff _).mpr (minpoly.monic hx)
  obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hQ hmon
  have hint : IsIntegral ℤ ((M : F) * x) := by
    refine ⟨Q, hQm, ?_⟩
    have h0 := Polynomial.scaleRoots_aeval_eq_zero (r := (M : ℚ)) (minpoly.aeval ℚ x)
    have hcast : Int.castRingHom ℚ = algebraMap ℤ ℚ := Subsingleton.elim _ _
    rw [← hP, ← hQmap, hcast, Polynomial.aeval_map_algebraMap, map_natCast] at h0
    rw [← Polynomial.aeval_def]
    exact h0
  exact ⟨M, ⟨(M : F) * x, hint⟩, hMcop, rfl⟩

/- English proof (translation)
Introduce `hE p _ G x hx`. Apply `integral_multiple_coprime` to reduce the goal to its premises. Apply `coeff_den` to reduce the goal to its premises. Introduce `τ`. Take `⟨w, σ, h | h⟩` from `hE p G τ`.

Rewrite using `[h x]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h x]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Gal.W2.fInt_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FInt := by
  intro hE p _ G x hx
  apply integral_multiple_coprime
  apply coeff_den
  intro τ
  obtain ⟨w, σ, h | h⟩ := hE p G τ
  · rw [h x]
    calc ‖σ (G.emb w x)‖ = ‖G.emb w x‖ := (spectralNorm_eq_of_equiv σ _).symm
      _ ≤ 1 := (hx w).1
  · rw [h x]
    calc ‖σ (G.emb w ((IsCMField.complexConj G.F) x))‖
        = ‖G.emb w ((IsCMField.complexConj G.F) x)‖ := (spectralNorm_eq_of_equiv σ _).symm
      _ ≤ 1 := (hx w).2
