import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open Polynomial

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem charPerm_dvd {G k : Type} [Group G] [Field k] (f : (G →* k) →₀ ℤ)
    (h : ∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f = 0) (ψ : G →* k) : ((ringChar k : ℕ) : ℤ) ∣ f ψ := by
  classical
  have hli := linearIndependent_monoidHom G k
  rw [linearIndependent_iff'] at hli
  have hsum : ∑ φ ∈ f.support, ((f φ : ℤ) : k) • ((φ : G →* k) : G → k) = 0 := by
    funext g
    have h0 := congrArg (fun u : k →₀ ℤ => u.sum (fun v z => (z : k) * v)) (h g)
    simp only [Finsupp.sum_zero_index] at h0
    rw [Finsupp.sum_mapDomain_index (by intro; simp) (by intro _ _ _; push_cast; ring)] at h0
    simpa [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h0
  by_cases hψ : ψ ∈ f.support
  · have := hli f.support (fun φ => ((f φ : ℤ) : k)) hsum ψ hψ
    exact (CharP.intCast_eq_zero_iff k (ringChar k) _).mp this
  · have : f ψ = 0 := by simpa using hψ
    rw [this]
    exact dvd_zero _

/- English proof (translation)
Consider separately whether the proposition holds or fails. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem charPerm_zero {G k : Type} [Group G] [Field k] (f : (G →* k) →₀ ℤ)
    (h : ∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f = 0) : f = 0 := by
  classical
  by_cases hp : ringChar k = 0
  · ext ψ
    have := charPerm_dvd f h ψ
    rw [hp] at this
    simpa using this
  · have hp1 : 1 < ringChar k :=
      ((CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hp).one_lt
    have key : ∀ n : ℕ, ∀ f : (G →* k) →₀ ℤ, (∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f = 0) →
        ∀ ψ, ((ringChar k : ℕ) : ℤ) ^ n ∣ f ψ := by
      intro n
      induction n with
      | zero => intro f _ ψ; simp
      | succ n ih =>
        intro f hf ψ
        let f1 : (G →* k) →₀ ℤ := Finsupp.mapRange (fun z : ℤ => z / ((ringChar k : ℕ) : ℤ)) (by simp) f
        have hf1 : f = ((ringChar k : ℕ) : ℤ) • f1 := by
          ext φ
          simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, f1]
          exact (Int.mul_ediv_cancel' (charPerm_dvd f hf φ)).symm
        have hf1' : ∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f1 = 0 := by
          intro g
          have := hf g
          rw [hf1, Finsupp.mapDomain_smul] at this
          exact (smul_eq_zero.mp this).resolve_left (by exact_mod_cast hp)
        have := ih f1 hf1' ψ
        rw [hf1, Finsupp.smul_apply, smul_eq_mul, pow_succ']
        exact mul_dvd_mul_left _ this
    ext ψ
    have hd := key (f ψ).natAbs f h ψ
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
    simpa [Int.natAbs_pow] using Nat.lt_pow_self (n := (f ψ).natAbs) hp1

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
private theorem charPerm_single {α ι : Type} [Fintype ι] (a b : ι → α) :
    Finset.univ.val.map a = Finset.univ.val.map b ↔
      (∑ i, Finsupp.single (a i) (1 : ℤ)) = ∑ i, Finsupp.single (b i) (1 : ℤ) := by
  classical
  have key : ∀ (s : Multiset α) (x : α),
      (s.map (fun y => Finsupp.single y (1 : ℤ))).sum x = (s.count x : ℤ) := by
    intro s x
    induction s using Multiset.induction_on with
    | empty => simp
    | cons y s ih =>
      by_cases hxy : y = x
      · subst hxy
        simp [Multiset.count_cons, ih]
        try ring
      · simp [Multiset.count_cons, ih, Finsupp.single_apply, hxy, Ne.symm hxy]
  have hsum : ∀ c : ι → α, (∑ i, Finsupp.single (c i) (1 : ℤ)) =
      ((Finset.univ.val.map c).map (fun y => Finsupp.single y (1 : ℤ))).sum := by
    intro c
    rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
    rfl
  constructor
  · intro h
    rw [hsum, hsum, h]
  · intro h
    refine Multiset.ext.mpr fun x => ?_
    have := DFunLike.congr_fun h x
    rw [hsum, hsum, key, key] at this
    exact_mod_cast this

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
private theorem charPerm_perm {α ι : Type} [Fintype ι] (a b : ι → α)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) : ∃ σ : Equiv.Perm ι, ∀ i, b i = a (σ i) := by
  classical
  have hc : ∀ c, Fintype.card {i // b i = c} = Fintype.card {i // a i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    simp only [Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_def, Finset.card_def,
      Finset.filter_val, Finset.filter_val]
    have e : ∀ d : ι → α, Multiset.filter (fun x => d x = c) Finset.univ.val =
        Multiset.filter (fun x => c = d x) Finset.univ.val :=
      fun d => Multiset.filter_congr (fun x _ => eq_comm)
    rw [e, e]
    convert this.symm
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), fun i => ?_⟩
  exact (Equiv.ofFiberEquiv_map _ i).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pr.charPerm :
    UpperTheory.V.Pr.CharPerm := by
  intro G k _ _ n χ χ' hχ
  classical
  let ψ : Fin n → (G →* k) := fun i => (Units.coeHom k).comp (χ i)
  let ψ' : Fin n → (G →* k) := fun i => (Units.coeHom k).comp (χ' i)
  have hr : ∀ a : Fin n → k, (∏ i, (X - C (a i))).roots = Finset.univ.val.map a := by
    intro a
    rw [Finset.prod_eq_multiset_prod]
    have : Finset.univ.val.map (fun i => X - C (a i)) = (Finset.univ.val.map a).map (fun x => X - C x) := by
      rw [Multiset.map_map]
      rfl
    rw [this, Polynomial.roots_multiset_prod_X_sub_C]
  have hroots : ∀ g, Finset.univ.val.map (fun i => ψ i g) = Finset.univ.val.map (fun i => ψ' i g) := by
    intro g
    have h1 := congrArg Polynomial.roots (hχ g)
    unfold UpperTheory.V.Pr.chPoly at h1
    rw [hr, hr] at h1
    exact h1
  let f : (G →* k) →₀ ℤ := (∑ i, Finsupp.single (ψ' i) (1 : ℤ)) - ∑ i, Finsupp.single (ψ i) 1
  have hf : ∀ g, Finsupp.mapDomain (fun φ : G →* k => φ g) f = 0 := by
    intro g
    simp only [f, Finsupp.mapDomain_sub, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single]
    rw [sub_eq_zero]
    exact (charPerm_single (fun i => ψ' i g) (fun i => ψ i g)).mp (hroots g).symm
  have hs : (∑ i, Finsupp.single (ψ i) (1 : ℤ)) = ∑ i, Finsupp.single (ψ' i) 1 :=
    (sub_eq_zero.mp (charPerm_zero f hf)).symm
  obtain ⟨σ, hσ⟩ := charPerm_perm ψ ψ' ((charPerm_single ψ ψ').mpr hs)
  refine ⟨σ, fun i => MonoidHom.ext fun g => Units.ext ?_⟩
  exact congrArg (fun φ : G →* k => φ g) (hσ i)
