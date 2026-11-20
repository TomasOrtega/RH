import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open Polynomial

/- English proof (translation)
Establish `hli` using `linearIndependent_monoidHom G k`. Rewrite `hli` using `[linearIndependent_iff']`. Establish `hsum : ∑ φ ∈ f.support, ((f φ : ℤ) : k) • ((φ : G →* k) : G → k) = 0`. Use function extensionality and compare the values at `g`. Establish `h0` using `congrArg (fun u : k →₀ ℤ => u.sum (fun v z => (z : k) * v)) (h g)`.

Simplify using `only [Finsupp.sum_zero_index] at h0`. Rewrite `h0` using `[Finsupp.sum_mapDomain_index (by intro; simp) (by intro _ _ _; push_cast; ring)]`. Simplify `h0` using `[Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hψ : ψ ∈ f.support`. Use `hli f.support (fun φ => ((f φ : ℤ) : k)) hsum ψ hψ` as an intermediate fact.

Conclude with `(CharP.intCast_eq_zero_iff k (ringChar k) _).mp this`. Establish `: f ψ = 0` using `by simpa using hψ`. Rewrite using `[this]`. Conclude with `dvd_zero _`.
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
Distinguish the cases in `hp : ringChar k = 0`. Use extensionality with `ψ`. Use `charPerm_dvd f h ψ` as an intermediate fact. Rewrite `this` using `[hp]`. Simplify using `using this`.

Establish `hp1 : 1 < ringChar k` using `((CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hp).one_lt`. Establish `key : ∀ n : ℕ, ∀ f : (G →* k) →₀ ℤ, (∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f = 0) → ∀ ψ, ((ringChar k : ℕ) : ℤ) ^ n ∣ f ψ`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro f _ ψ`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `f hf ψ`. Set `f1 : (G →* k) →₀ ℤ` to `Finsupp.mapRange (fun z : ℤ => z / ((ringChar k : ℕ) : ℤ)) (by simp) f`. Establish `hf1 : f = ((ringChar k : ℕ) : ℤ) • f1`.

Use extensionality with `φ`. Simplify using `only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, f1]`. Conclude with `(Int.mul_ediv_cancel' (charPerm_dvd f hf φ)).symm`. Establish `hf1' : ∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f1 = 0`. Introduce `g`.

Use `hf g` as an intermediate fact. Rewrite `this` using `[hf1, Finsupp.mapDomain_smul]`. Conclude with `(smul_eq_zero.mp this).resolve_left (by exact_mod_cast hp)`. Use `ih f1 hf1' ψ` as an intermediate fact. Rewrite using `[hf1, Finsupp.smul_apply, smul_eq_mul, pow_succ']`.

Conclude with `mul_dvd_mul_left _ this`. Use extensionality with `ψ`. Establish `hd` using `key (f ψ).natAbs f h ψ`. Apply `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd` to reduce the goal to its premises. Simplify `Nat.lt_pow_self (n := (f ψ).natAbs) hp1` using `[Int.natAbs_pow]`.
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
Establish `key : ∀ (s : Multiset α) (x : α), (s.map (fun y => Finsupp.single y (1 : ℤ))).sum x = (s.count x : ℤ)`. Introduce `s x`. Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons y s ih`.

Distinguish the cases in `hxy : y = x`. Substitute `hxy` using the available equality. Simplify using `[Multiset.count_cons, ih]`. Apply the tactic sequence `try ring`. Simplify using `[Multiset.count_cons, ih, Finsupp.single_apply, hxy, Ne.symm hxy]`.

Establish `hsum : ∀ c : ι → α, (∑ i, Finsupp.single (c i) (1 : ℤ)) = ((Finset.univ.val.map c).map (fun y => Finsupp.single y (1 : ℤ))).sum`. Introduce `c`. Rewrite using `[Finset.sum_eq_multiset_sum, Multiset.map_map]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[hsum, hsum, h]`. Introduce `h`. Use `Multiset.ext.mpr fun x => ?_` and prove the remaining obligations. Use `DFunLike.congr_fun h x` as an intermediate fact.

Rewrite `this` using `[hsum, hsum, key, key]`. Conclude with `this` after adjusting the coercions.
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
Establish `hc : ∀ c, Fintype.card {i // b i = c} = Fintype.card {i // a i = c}`. Introduce `c`. Use `congrArg (Multiset.count c) h` as an intermediate fact. Simplify using `only [Multiset.count_map] at this`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype, Finset.card_def, Finset.card_def, Finset.filter_val, Finset.filter_val]`.

Establish `e : ∀ d : ι → α, Multiset.filter (fun x => d x = c) Finset.univ.val = Multiset.filter (fun x => c = d x) Finset.univ.val` using `fun d => Multiset.filter_congr (fun x _ => eq_comm)`. Rewrite using `[e, e]`. Use `this.symm` and compare the differences between its conclusion and the goal. Use `⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), fun i => ?_⟩` and prove the remaining obligations. Conclude with `(Equiv.ofFiberEquiv_map _ i).symm`.
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
Introduce `G k _ _ n χ χ' hχ`. Set `ψ : Fin n → (G →* k)` to `fun i => (Units.coeHom k).comp (χ i)`. Set `ψ' : Fin n → (G →* k)` to `fun i => (Units.coeHom k).comp (χ' i)`. Establish `hr : ∀ a : Fin n → k, (∏ i, (X - C (a i))).roots = Finset.univ.val.map a`. Introduce `a`.

Rewrite using `[Finset.prod_eq_multiset_prod]`. Establish `: Finset.univ.val.map (fun i => X - C (a i)) = (Finset.univ.val.map a).map (fun x => X - C x)`. Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression. Rewrite using `[this, Polynomial.roots_multiset_prod_X_sub_C]`.

Establish `hroots : ∀ g, Finset.univ.val.map (fun i => ψ i g) = Finset.univ.val.map (fun i => ψ' i g)`. Introduce `g`. Establish `h1` using `congrArg Polynomial.roots (hχ g)`. Unfold `UpperTheory.V.Pr.chPoly at h1`. Rewrite `h1` using `[hr, hr]`.

Conclude with `h1`. Set `f : (G →* k) →₀ ℤ` to `(∑ i, Finsupp.single (ψ' i) (1 : ℤ)) - ∑ i, Finsupp.single (ψ i) 1`. Establish `hf : ∀ g, Finsupp.mapDomain (fun φ : G →* k => φ g) f = 0`. Introduce `g`. Simplify using `only [f, Finsupp.mapDomain_sub, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single]`.

Rewrite using `[sub_eq_zero]`. Conclude with `(charPerm_single (fun i => ψ' i g) (fun i => ψ i g)).mp (hroots g).symm`. Establish `hs : (∑ i, Finsupp.single (ψ i) (1 : ℤ)) = ∑ i, Finsupp.single (ψ' i) 1` using `(sub_eq_zero.mp (charPerm_zero f hf)).symm`. Take `⟨σ, hσ⟩` from `charPerm_perm ψ ψ' ((charPerm_single ψ ψ').mpr hs)`. Use `⟨σ, fun i => MonoidHom.ext fun g => Units.ext ?_⟩` and prove the remaining obligations.

Conclude with `congrArg (fun φ : G →* k => φ g) (hσ i)`.
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
