import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompatibleSectionsGlueHomogeneousStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.Lift

variable {R : Type} [CommRing R] (I : Ideal R) (N : ℕ)

def iota : reesAlgebra I →+* Polynomial (MvPolynomial (Fin (N + 1)) R) :=
  (Polynomial.mapRingHom (C : R →+* MvPolynomial (Fin (N + 1)) R)).comp
    (reesAlgebra I).val.toRingHom

def Psi : MvPolynomial (Fin (N + 1)) (reesAlgebra I) →+*
    Polynomial (MvPolynomial (Fin (N + 1)) R) :=
  eval₂Hom (iota I N) (fun i => Polynomial.C (X i))

def phi (d : ℕ) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    MvPolynomial (Fin (N + 1)) R :=
  (Psi I N p).coeff d

variable {I N}

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.GE.Lift.phi`. Rewrite using `[map_add, Polynomial.coeff_add]`.
-/
theorem phi_add (d : ℕ) (p q : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (p + q) = phi I N d p + phi I N d q := by
  unfold GlobalTheory.CompanionTheory.GE.Lift.phi
  rw [map_add, Polynomial.coeff_add]

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.GE.Lift.phi`. Rewrite using `[map_sub, Polynomial.coeff_sub]`.
-/
theorem phi_sub (d : ℕ) (p q : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (p - q) = phi I N d p - phi I N d q := by
  unfold GlobalTheory.CompanionTheory.GE.Lift.phi
  rw [map_sub, Polynomial.coeff_sub]

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.GE.Lift.phi`. Rewrite using `[map_zero, Polynomial.coeff_zero]`.
-/
theorem phi_zero (d : ℕ) : phi I N d 0 = 0 := by
  unfold GlobalTheory.CompanionTheory.GE.Lift.phi
  rw [map_zero, Polynomial.coeff_zero]

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.GE.Lift.phi`. Rewrite using `[map_mul, GlobalTheory.CompanionTheory.GE.Lift.Psi, MvPolynomial.eval₂Hom_X', Polynomial.coeff_C_mul]`.
-/
theorem phi_X_mul (d : ℕ) (i : Fin (N + 1)) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (X i * p) = X i * phi I N d p := by
  unfold GlobalTheory.CompanionTheory.GE.Lift.phi
  rw [map_mul, GlobalTheory.CompanionTheory.GE.Lift.Psi, MvPolynomial.eval₂Hom_X', Polynomial.coeff_C_mul]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ', mul_assoc, GlobalTheory.CompanionTheory.GE.Lift.phi_X_mul, ih, ← mul_assoc, ← pow_succ']`.
-/
theorem phi_X_pow_mul (d : ℕ) (i : Fin (N + 1)) (m : ℕ)
    (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (X i ^ m * p) = X i ^ m * phi I N d p := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', mul_assoc, GlobalTheory.CompanionTheory.GE.Lift.phi_X_mul, ih, ← mul_assoc, ← pow_succ']

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.GE.Lift.phi`. Rewrite using `[map_mul, Polynomial.coeff_mul]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.GE.Lift.Psi, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, GlobalTheory.CompanionTheory.GE.Lift.iota, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map]`. Both sides reduce to the same expression.
-/
theorem phi_C_mul (d : ℕ) (b : reesAlgebra I) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (C b * p) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal d,
      C ((b : Polynomial R).coeff x.1) * phi I N x.2 p := by
  unfold GlobalTheory.CompanionTheory.GE.Lift.phi
  rw [map_mul, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.CompanionTheory.GE.Lift.Psi, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
    GlobalTheory.CompanionTheory.GE.Lift.iota, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rfl

/- English proof (translation)
Establish `hprod : (s.prod fun i k => (Polynomial.C (X i) : Polynomial (MvPolynomial (Fin (N + 1)) R)) ^ k) = Polynomial.C (s.prod fun i k => X i ^ k)`. Simplify using `only [Finsupp.prod, map_prod, map_pow]`. Rewrite using `[GlobalTheory.CompanionTheory.GE.Lift.phi, GlobalTheory.CompanionTheory.GE.Lift.Psi, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, hprod, Polynomial.coeff_mul_C, GlobalTheory.CompanionTheory.GE.Lift.iota, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_m …`. Both sides reduce to the same expression.
-/
theorem phi_monomial (d : ℕ) (s : Fin (N + 1) →₀ ℕ) (b : reesAlgebra I) :
    phi I N d (monomial s b) = monomial s ((b : Polynomial R).coeff d) := by
  have hprod : (s.prod fun i k => (Polynomial.C (X i) : Polynomial (MvPolynomial (Fin (N + 1)) R)) ^ k) =
      Polynomial.C (s.prod fun i k => X i ^ k) := by
    simp only [Finsupp.prod, map_prod, map_pow]
  rw [GlobalTheory.CompanionTheory.GE.Lift.phi, GlobalTheory.CompanionTheory.GE.Lift.Psi, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_monomial, hprod, Polynomial.coeff_mul_C, GlobalTheory.CompanionTheory.GE.Lift.iota,
    RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map, MvPolynomial.monomial_eq]
  rfl

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial u b`. Rewrite using `[GlobalTheory.CompanionTheory.GE.Lift.phi_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]`. Apply the tactic sequence `split_ifs <;> simp`. Consider the case `add p q hp hq`.

Rewrite using `[GlobalTheory.CompanionTheory.GE.Lift.phi_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]`. Simplify using the standard rewrite rules.
-/
theorem coeff_phi (d : ℕ) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I))
    (s : Fin (N + 1) →₀ ℕ) :
    coeff s (phi I N d p) = ((coeff s p : reesAlgebra I) : Polynomial R).coeff d := by
  induction p using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [GlobalTheory.CompanionTheory.GE.Lift.phi_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq =>
    rw [GlobalTheory.CompanionTheory.GE.Lift.phi_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
    simp

/- English proof (translation)
Rewrite using `[mem_map_C_iff]`. Introduce `s`. Rewrite using `[coeff_phi]`. Conclude with `(mem_reesAlgebra_iff I _).1 (coeff s p).2 d`.
-/
theorem phi_mem_map (d : ℕ) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d p ∈ (I ^ d).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  rw [mem_map_C_iff]
  intro s
  rw [coeff_phi]
  exact (mem_reesAlgebra_iff I _).1 (coeff s p).2 d

/- English proof (translation)
Introduce `s hs`. Apply `hp` to reduce the goal to its premises. Introduce `h0`. Apply `hs` to reduce the goal to its premises. Rewrite using `[coeff_phi, h0]`.

Simplify using the standard rewrite rules.
-/
theorem phi_isHomogeneous (d n : ℕ) {p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)}
    (hp : p.IsHomogeneous n) : (phi I N d p).IsHomogeneous n := by
  intro s hs
  apply hp
  intro h0
  apply hs
  rw [coeff_phi, h0]
  simp

/- English proof (translation)
Use extensionality with `s`. Simplify using `only [GlobalTheory.CompanionTheory.GE.Lift.coeff_phi, MvPolynomial.coeff_homogeneousComponent]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem phi_homogeneousComponent (d e : ℕ) (p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)) :
    phi I N d (homogeneousComponent e p) = homogeneousComponent e (phi I N d p) := by
  ext s
  simp only [GlobalTheory.CompanionTheory.GE.Lift.coeff_phi, MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp

/- English proof (translation)
Establish `hmem : ∀ s, Polynomial.monomial d (coeff s t) ∈ reesAlgebra I`. Introduce `s`. Rewrite using `[mem_reesAlgebra_iff]`. Introduce `i`. Rewrite using `[Polynomial.coeff_monomial]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `MvPolynomial.mem_map_C_iff.1 ht s`. Conclude with `zero_mem _`. Use `⟨∑ s ∈ t.support, monomial s (⟨Polynomial.monomial d (coeff s t), hmem s⟩ : reesAlgebra I), fun s => ?_⟩` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[MvPolynomial.notMem_support_iff.1 h]`.

Simplify using the standard rewrite rules.
-/
theorem exists_lift (d : ℕ) (t : MvPolynomial (Fin (N + 1)) R)
    (ht : t ∈ (I ^ d).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) :
    ∃ τ : MvPolynomial (Fin (N + 1)) (reesAlgebra I),
      ∀ s, ((coeff s τ : reesAlgebra I) : Polynomial R) = Polynomial.monomial d (coeff s t) := by
  have hmem : ∀ s, Polynomial.monomial d (coeff s t) ∈ reesAlgebra I := by
    intro s
    rw [mem_reesAlgebra_iff]
    intro i
    rw [Polynomial.coeff_monomial]
    split_ifs with h
    · subst h
      exact MvPolynomial.mem_map_C_iff.1 ht s
    · exact zero_mem _
  refine ⟨∑ s ∈ t.support, monomial s (⟨Polynomial.monomial d (coeff s t), hmem s⟩ : reesAlgebra I),
    fun s => ?_⟩
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h]
    simp

/- English proof (translation)
Use extensionality with `s`. Rewrite using `[GlobalTheory.CompanionTheory.GE.Lift.coeff_phi, h, Polynomial.coeff_monomial]`. Distinguish the cases in `hd : d' = d`. Substitute `hd` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg (Ne.symm hd), if_neg hd, MvPolynomial.coeff_zero]`.
-/
theorem phi_lift {d : ℕ} {t : MvPolynomial (Fin (N + 1)) R}
    {τ : MvPolynomial (Fin (N + 1)) (reesAlgebra I)}
    (h : ∀ s, ((coeff s τ : reesAlgebra I) : Polynomial R) = Polynomial.monomial d (coeff s t))
    (d' : ℕ) : phi I N d' τ = if d' = d then t else 0 := by
  ext s
  rw [GlobalTheory.CompanionTheory.GE.Lift.coeff_phi, h, Polynomial.coeff_monomial]
  by_cases hd : d' = d
  · subst hd
    simp
  · rw [if_neg (Ne.symm hd), if_neg hd, MvPolynomial.coeff_zero]

/- English proof (translation)
Introduce `s hs`. Apply `ht` to reduce the goal to its premises. Introduce `h0`. Apply `hs` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[h, h0]`. Simplify using the standard rewrite rules.
-/
theorem lift_isHomogeneous {d n : ℕ} {t : MvPolynomial (Fin (N + 1)) R}
    {τ : MvPolynomial (Fin (N + 1)) (reesAlgebra I)}
    (h : ∀ s, ((coeff s τ : reesAlgebra I) : Polynomial R) = Polynomial.monomial d (coeff s t))
    (ht : t.IsHomogeneous n) : τ.IsHomogeneous n := by
  intro s hs
  apply ht
  intro h0
  apply hs
  apply Subtype.ext
  rw [h, h0]
  simp

/- English proof (translation)
Establish `hstep : ∀ e, I.map (C : R →+* MvPolynomial (Fin (N + 1)) R) * L e ≤ L (e + 1)`. Introduce `e`. Rewrite using `[Ideal.mul_le]`. Introduce `a ha f hf`. Apply `hsat (e + 1)` to reduce the goal to its premises.

Introduce `j`. Take `⟨m, hm⟩` from `hcompat e f hf j`. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 hm`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hav : a * v ∈ L (e + 1)`.

Use `hbase (e + 1) ?_` and prove the remaining obligations. Rewrite using `[pow_succ', Ideal.map_mul]`. Conclude with `Ideal.mul_mem_mul ha hv`. Establish `hsplit : X j ^ m * (a * f) = a * u + a * v`. Rewrite using `[← mul_add, huv]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ hu) hav`. Proceed by induction on `k generalizing e with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_succ, mul_assoc]`. Use `_ ≤ (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L (e + 1) := Ideal.mul_mono_right (hstep e)`. Use `_ ≤ L (e + 1 + k) := ih (e + 1)`.

Use `_ = L (e + (k + 1)) := by rw [add_assoc, add_comm 1 k]`.
-/
theorem pow_mul_le (I : Ideal R) (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R))
    (hbase : ∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e)
    (hsat : ∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ L e) → f ∈ L e)
    (hcompat : ∀ e, ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      L (e + 1) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (k e : ℕ) :
    (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k) := by
  have hstep : ∀ e, I.map (C : R →+* MvPolynomial (Fin (N + 1)) R) * L e ≤ L (e + 1) := by
    intro e
    rw [Ideal.mul_le]
    intro a ha f hf
    apply hsat (e + 1)
    intro j
    obtain ⟨m, hm⟩ := hcompat e f hf j
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hm
    refine ⟨m, ?_⟩
    have hav : a * v ∈ L (e + 1) := by
      refine hbase (e + 1) ?_
      rw [pow_succ', Ideal.map_mul]
      exact Ideal.mul_mem_mul ha hv
    have hsplit : X j ^ m * (a * f) = a * u + a * v := by
      rw [← mul_add, huv]
      ring
    rw [hsplit]
    exact add_mem (Ideal.mul_mem_left _ _ hu) hav
  induction k generalizing e with
  | zero => simp
  | succ k ih =>
    calc (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ (k + 1) * L e
        = (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k *
            ((I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) * L e) := by
          rw [pow_succ, mul_assoc]
      _ ≤ (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L (e + 1) :=
          Ideal.mul_mono_right (hstep e)
      _ ≤ L (e + 1 + k) := ih (e + 1)
      _ = L (e + (k + 1)) := by rw [add_assoc, add_comm 1 k]

def reesIdeal (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R))
    (hL : ∀ k e, (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k)) :
    Ideal (MvPolynomial (Fin (N + 1)) (reesAlgebra I)) where
  carrier := {p | ∀ d, phi I N d p ∈ L d}
  add_mem' := fun hp hq d => by
    rw [phi_add]
    exact add_mem (hp d) (hq d)
  zero_mem' := fun d => by
    rw [phi_zero]
    exact zero_mem _
  smul_mem' := fun c p hp => by
    show ∀ d, phi I N d (c * p) ∈ L d
    induction c using MvPolynomial.induction_on with
    | C b =>
      intro d
      rw [phi_C_mul]
      refine sum_mem fun x hx => ?_
      have hx' : x.2 + x.1 = d := by
        rw [add_comm]
        exact Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [← hx']
      refine hL x.1 x.2 ?_
      refine Ideal.mul_mem_mul ?_ (hp x.2)
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).1 b.2 x.1)
    | add a b ha hb =>
      intro d
      rw [add_mul, phi_add]
      exact add_mem (ha d) (hb d)
    | mul_X a i ha =>
      intro d
      rw [mul_comm a, mul_assoc, phi_X_mul]
      exact Ideal.mul_mem_left _ _ (ha d)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_reesIdeal {L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)}
    {hL : ∀ k e, (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k)}
    {p : MvPolynomial (Fin (N + 1)) (reesAlgebra I)} :
    p ∈ reesIdeal L hL ↔ ∀ d, phi I N d p ∈ L d :=
  Iff.rfl

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.GE.HomogIdeal at hhom ⊢`. Introduce `e p hp`. Rewrite `hp`, the goal using `[GlobalTheory.CompanionTheory.GE.Lift.mem_reesIdeal]`. Introduce `d`. Rewrite using `[GlobalTheory.CompanionTheory.GE.Lift.phi_homogeneousComponent]`.

Conclude with `hhom d e _ (hp d)`.
-/
theorem reesIdeal_homog {L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)}
    (hhom : ∀ e, HomogIdeal (L e))
    (hL : ∀ k e, (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k)) :
    HomogIdeal (reesIdeal L hL) := by
  unfold GlobalTheory.CompanionTheory.GE.HomogIdeal at hhom ⊢
  intro e p hp
  rw [GlobalTheory.CompanionTheory.GE.Lift.mem_reesIdeal] at hp ⊢
  intro d
  rw [GlobalTheory.CompanionTheory.GE.Lift.phi_homogeneousComponent]
  exact hhom d e _ (hp d)

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.GE.HomogIdeal`. Introduce `d f hf`. Rewrite `hf`, the goal using `[MvPolynomial.mem_map_C_iff]`. Introduce `m`. Rewrite using `[MvPolynomial.coeff_homogeneousComponent]`.

Use `split_ifs`. Conclude with `hf m`. Conclude with `zero_mem _`.
-/
theorem homogIdeal_map (J : Ideal R) :
    HomogIdeal (J.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) := by
  unfold GlobalTheory.CompanionTheory.GE.HomogIdeal
  intro d f hf
  rw [MvPolynomial.mem_map_C_iff] at hf ⊢
  intro m
  rw [MvPolynomial.coeff_homogeneousComponent]
  split_ifs
  · exact hf m
  · exact zero_mem _

/- English proof (translation)
Introduce `R _ _ I N L hhom hbase hsat hcompat`. Establish `hL : ∀ k e, (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k)` using `GlobalTheory.CompanionTheory.GE.Lift.pow_mul_le I L hbase hsat hcompat`. Take `⟨n₀, hn₀⟩` from `GlobalTheory.T.compatible_sections_glue_homogeneous (reesAlgebra I) N (GlobalTheory.CompanionTheory.GE.Lift.reesIdeal L hL) (GlobalTheory.CompanionTheory.GE.Lift.reesIdeal_homog hhom hL)`. Use `⟨n₀, fun e n hn f hf hfh => ?_⟩` and prove the remaining obligations. Use `choose m hm using hcompat e f hf`.

Use `set k := Finset.univ.sup m with hk`. Establish `hv : ∀ i, ∃ v ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R), v.IsHomogeneous (n + k) ∧ X i ^ k * f - v ∈ L (e + 1)`. Introduce `i`. Take `⟨c, hc⟩ : ∃ c, k = m i + c` from `Nat.exists_eq_add_of_le (Finset.le_sup (f := m) (Finset.mem_univ i))`. Establish `hmem : X i ^ k * f ∈ L (e + 1) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)`.

Establish `h` using `Ideal.mul_mem_left _ (X i ^ c) (hm i)`. Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hc, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨u, hu, w, hw, huw⟩` from `Submodule.mem_sup.1 hmem`.

Establish `hXf : (X i ^ k * f).IsHomogeneous (n + k)`. Rewrite using `[add_comm n k]`. Conclude with `(MvPolynomial.isHomogeneous_X_pow i k).mul hfh`. Use `⟨homogeneousComponent (n + k) w, GlobalTheory.CompanionTheory.GE.Lift.homogIdeal_map (I ^ (e + 1)) (n + k) w hw, MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_⟩` and prove the remaining obligations. Establish `hfix : homogeneousComponent (n + k) (X i ^ k * f) = X i ^ k * f`.

Rewrite using `[MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2 hXf), if_pos rfl]`. Rewrite using `[← hfix, ← map_sub, ← huw, add_sub_cancel_right]`. Conclude with `hhom (e + 1) (n + k) u hu`. Use `choose v hvI hvh hvL using hv`. Use `choose τ hτ using fun i => GlobalTheory.CompanionTheory.GE.Lift.exists_lift (e + 1) (v i) (hvI i)`.

Take `⟨g, hg, hgm⟩` from `hn₀ n hn k τ (fun i => GlobalTheory.CompanionTheory.GE.Lift.lift_isHomogeneous (hτ i) (hvh i)) (by`. Introduce `i j`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, one_mul, GlobalTheory.CompanionTheory.GE.Lift.mem_reesIdeal]`. Introduce `d`.

Rewrite using `[GlobalTheory.CompanionTheory.GE.Lift.phi_sub, GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul, GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul, GlobalTheory.CompanionTheory.GE.Lift.phi_lift (hτ i), GlobalTheory.CompanionTheory.GE.Lift.phi_lift (hτ j)]`. Use `split_ifs with hd`. Substitute `hd` using the available equality. Establish `h` using `sub_mem (Ideal.mul_mem_left _ (X i ^ k) (hvL j)) (Ideal.mul_mem_left _ (X j ^ k) (hvL i))`. Use `h using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Use the proof step `simp)`. Use `⟨f - GlobalTheory.CompanionTheory.GE.Lift.phi I N (e + 1) g, ?_, hfh.sub (GlobalTheory.CompanionTheory.GE.Lift.phi_isHomogeneous (e + 1) n hg), ?_⟩` and prove the remaining obligations. Apply `hsat (e + 1)` to reduce the goal to its premises. Introduce `i`.

Take `⟨p, hp⟩` from `hgm i`. Use `⟨p + k, ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CompanionTheory.GE.Lift.mem_reesIdeal.1 hp (e + 1)`. Rewrite `h1` using `[GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul, GlobalTheory.CompanionTheory.GE.Lift.phi_sub, GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul, GlobalTheory.CompanionTheory.GE.Lift.phi_lift (hτ i), if_pos rfl]`. Establish `h` using `sub_mem (Ideal.mul_mem_left _ (X i ^ p) (hvL i)) h1`.

Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sub_sub_cancel]`. Conclude with `GlobalTheory.CompanionTheory.GE.Lift.phi_mem_map (e + 1) g`.
-/
theorem uniform_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ L e) → f ∈ L e) →
    (∀ e, ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      L (e + 1) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ n₀ : ℕ, ∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  intro R _ _ I N L hhom hbase hsat hcompat
  have hL : ∀ k e, (I.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ^ k * L e ≤ L (e + k) :=
    GlobalTheory.CompanionTheory.GE.Lift.pow_mul_le I L hbase hsat hcompat
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.compatible_sections_glue_homogeneous (reesAlgebra I) N
    (GlobalTheory.CompanionTheory.GE.Lift.reesIdeal L hL) (GlobalTheory.CompanionTheory.GE.Lift.reesIdeal_homog hhom hL)
  refine ⟨n₀, fun e n hn f hf hfh => ?_⟩
  choose m hm using hcompat e f hf
  set k := Finset.univ.sup m with hk
  have hv : ∀ i, ∃ v ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R),
      v.IsHomogeneous (n + k) ∧ X i ^ k * f - v ∈ L (e + 1) := by
    intro i
    obtain ⟨c, hc⟩ : ∃ c, k = m i + c :=
      Nat.exists_eq_add_of_le (Finset.le_sup (f := m) (Finset.mem_univ i))
    have hmem : X i ^ k * f ∈
        L (e + 1) ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
      have h := Ideal.mul_mem_left _ (X i ^ c) (hm i)
      convert h using 1
      rw [hc, pow_add]
      ring
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hmem
    have hXf : (X i ^ k * f).IsHomogeneous (n + k) := by
      rw [add_comm n k]
      exact (MvPolynomial.isHomogeneous_X_pow i k).mul hfh
    refine ⟨homogeneousComponent (n + k) w,
      GlobalTheory.CompanionTheory.GE.Lift.homogIdeal_map (I ^ (e + 1)) (n + k) w hw,
      MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_⟩
    have hfix : homogeneousComponent (n + k) (X i ^ k * f) = X i ^ k * f := by
      rw [MvPolynomial.homogeneousComponent_of_mem
        ((MvPolynomial.mem_homogeneousSubmodule _ _).2 hXf), if_pos rfl]
    rw [← hfix, ← map_sub, ← huw, add_sub_cancel_right]
    exact hhom (e + 1) (n + k) u hu
  choose v hvI hvh hvL using hv
  choose τ hτ using fun i => GlobalTheory.CompanionTheory.GE.Lift.exists_lift (e + 1) (v i) (hvI i)
  obtain ⟨g, hg, hgm⟩ := hn₀ n hn k τ
    (fun i => GlobalTheory.CompanionTheory.GE.Lift.lift_isHomogeneous (hτ i) (hvh i)) (by
      intro i j
      refine ⟨0, ?_⟩
      rw [pow_zero, one_mul, GlobalTheory.CompanionTheory.GE.Lift.mem_reesIdeal]
      intro d
      rw [GlobalTheory.CompanionTheory.GE.Lift.phi_sub, GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul, GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul,
        GlobalTheory.CompanionTheory.GE.Lift.phi_lift (hτ i), GlobalTheory.CompanionTheory.GE.Lift.phi_lift (hτ j)]
      split_ifs with hd
      · subst hd
        have h := sub_mem (Ideal.mul_mem_left _ (X i ^ k) (hvL j))
          (Ideal.mul_mem_left _ (X j ^ k) (hvL i))
        convert h using 1
        ring
      · simp)
  refine ⟨f - GlobalTheory.CompanionTheory.GE.Lift.phi I N (e + 1) g, ?_,
    hfh.sub (GlobalTheory.CompanionTheory.GE.Lift.phi_isHomogeneous (e + 1) n hg), ?_⟩
  · apply hsat (e + 1)
    intro i
    obtain ⟨p, hp⟩ := hgm i
    refine ⟨p + k, ?_⟩
    have h1 := GlobalTheory.CompanionTheory.GE.Lift.mem_reesIdeal.1 hp (e + 1)
    rw [GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul, GlobalTheory.CompanionTheory.GE.Lift.phi_sub, GlobalTheory.CompanionTheory.GE.Lift.phi_X_pow_mul,
      GlobalTheory.CompanionTheory.GE.Lift.phi_lift (hτ i), if_pos rfl] at h1
    have h := sub_mem (Ideal.mul_mem_left _ (X i ^ p) (hvL i)) h1
    convert h using 1
    ring
  · rw [sub_sub_cancel]
    exact GlobalTheory.CompanionTheory.GE.Lift.phi_mem_map (e + 1) g

end GlobalTheory.CompanionTheory.GE.Lift
