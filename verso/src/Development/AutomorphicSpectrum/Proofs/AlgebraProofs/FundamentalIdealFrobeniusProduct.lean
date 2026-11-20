import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusChainCarry
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalCharacter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalCharacterIdealPowers
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowersStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.ROm

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
  {F : Type} [Field F]

/- English proof (translation)
Establish `: LinearMap.toSpanSingleton R (F → C) (fun a => algebraMap R C (χ a)) r = fun a => algebraMap R C (r * χ a)`. Use function extensionality and compare the values at `a`. Simplify using `[Algebra.smul_def]`. Rewrite using `[xIdeal, Submodule.mem_comap, this]`.
-/
theorem mem_x_ideal_iff (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C (r * χ a)) ∈ M := by
  have : LinearMap.toSpanSingleton R (F → C) (fun a => algebraMap R C (χ a)) r =
      fun a => algebraMap R C (r * χ a) := by
    funext a; simp [Algebra.smul_def]
  rw [xIdeal, Submodule.mem_comap, this]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_aug (M : Submodule R (F → C)) (g : F → C) :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

/- English proof (translation)
Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 h`. Rewrite using `[map_mul, map_mul]`. Conclude with `mul_le_of_le_one_left' (hv.map_le_one s)`.
-/
theorem v_le_of_mem (hv : v.Integers R) {a b : R} (h : a ∈ Ideal.span {b}) :
    v (algebraMap R C a) ≤ v (algebraMap R C b) := by
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 h
  rw [map_mul, map_mul]
  exact mul_le_of_le_one_left' (hv.map_le_one s)

/- English proof (translation)
The claim follows from `le_antisymm (v_le_of_mem hv (h ▸ Ideal.mem_span_singleton_self a)) (v_le_of_mem hv (h ▸ Ideal.mem_span_singleton_self b))`.
-/
theorem v_eq_of_span (hv : v.Integers R) {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    v (algebraMap R C a) = v (algebraMap R C b) :=
  le_antisymm (v_le_of_mem hv (h ▸ Ideal.mem_span_singleton_self a))
    (v_le_of_mem hv (h ▸ Ideal.mem_span_singleton_self b))

/- English proof (translation)
Set `T : Submodule R C` to `{ carrier := {x | v x ≤ b} add_mem' := fun hx hy => v.map_add_le hx hy zero_mem' := by simp smul_mem' := fun r x hx => by`. Express the relevant statement in the definitionally equal form `v (r • x) ≤ b`. Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `(mul_le_of_le_one_left' (hv.map_le_one r)).trans hx }`. Establish `: sqIdeal (Submodule.span R s) ≤ T.comap l`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, g', hg', rfl⟩`. Establish `h1 : Submodule.span R s * Submodule.span R s ≤ T.comap l`. Rewrite using `[Submodule.span_mul_span]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, ha, a', ha', rfl⟩`. Conclude with `h a ha a' ha'`. Conclude with `h1 (Submodule.mul_mem_mul hg hg')`. Conclude with `fun g hg => this hg`.
-/
theorem sq_bound (hv : v.Integers R) {X : Type} (s : Set (X → C)) (l : (X → C) →ₗ[R] C)
    (b : NNReal) (h : ∀ g ∈ s, ∀ g' ∈ s, v (l (g * g')) ≤ b) :
    ∀ g ∈ sqIdeal (Submodule.span R s), v (l g) ≤ b := by
  let T : Submodule R C :=
    { carrier := {x | v x ≤ b}
      add_mem' := fun hx hy => v.map_add_le hx hy
      zero_mem' := by simp
      smul_mem' := fun r x hx => by
        change v (r • x) ≤ b
        rw [Algebra.smul_def, map_mul]
        exact (mul_le_of_le_one_left' (hv.map_le_one r)).trans hx }
  have : sqIdeal (Submodule.span R s) ≤ T.comap l := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, g', hg', rfl⟩
    have h1 : Submodule.span R s * Submodule.span R s ≤ T.comap l := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, a', ha', rfl⟩
      exact h a ha a' ha'
    exact h1 (Submodule.mul_mem_mul hg hg')
  exact fun g hg => this hg

variable [Fintype F] [DecidableEq F]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hg`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Use `(mem_aug _ _).2 ⟨AA.mul_mem _ _ ih.1 hg.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.mul_apply, ((mem_aug _ _).1 hg).2, mul_zero]`.
-/
theorem pow_mem_aug (AA : HopfOrder (C := C) R F) {g : F → C} (hg : g ∈ augIdeal AA.carrier)
    (k : ℕ) : g ^ (k + 1) ∈ augIdeal AA.carrier := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [pow_succ]
    refine (mem_aug _ _).2 ⟨AA.mul_mem _ _ ih.1 hg.1, ?_⟩
    rw [Pi.mul_apply, ((mem_aug _ _).1 hg).2, mul_zero]

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, k = j + 1 + 1` from `⟨k - 2, by omega⟩`. Establish `hg : (fun a => algebraMap R C (c * χ a)) ∈ augIdeal AA.carrier` using `(mem_aug _ _).2 ⟨(mem_x_ideal_iff _ _ _).1 hc, by simp [MulChar.map_zero]⟩`. Use `Submodule.subset_span ⟨_, pow_mem_aug AA hg j, _, hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Rewrite using `[← pow_succ, Pi.pow_apply, MulChar.pow_apply' _ (by omega), ← mul_pow, map_pow]`.
-/
theorem pow_mem_sq (AA : HopfOrder (C := C) R F) (χ : MulChar F R) {c : R}
    (hc : c ∈ xIdeal AA.carrier χ) {k : ℕ} (hk : 2 ≤ k) :
    (fun a => algebraMap R C (c ^ k * (χ ^ k) a)) ∈ sqIdeal (augIdeal AA.carrier) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 2, by omega⟩
  have hg : (fun a => algebraMap R C (c * χ a)) ∈ augIdeal AA.carrier :=
    (mem_aug _ _).2 ⟨(mem_x_ideal_iff _ _ _).1 hc, by simp [MulChar.map_zero]⟩
  refine Submodule.subset_span ⟨_, pow_mem_aug AA hg j, _, hg, ?_⟩
  funext a
  rw [← pow_succ, Pi.pow_apply, MulChar.pow_apply' _ (by omega), ← mul_pow, map_pow]

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, g', hg', rfl⟩`. Conclude with `AA.mul_mem _ _ hg.1 hg'.1`.
-/
theorem sq_le (AA : HopfOrder (C := C) R F) : sqIdeal (augIdeal AA.carrier) ≤ AA.carrier := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, g', hg', rfl⟩
  exact AA.mul_mem _ _ hg.1 hg'.1

omit [Fintype F] [DecidableEq F] in
/- English proof (translation)
Simplify using `only [smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eig_fun (χ : MulChar F R) (r : R) (a x : F) :
    algebraMap R C (r * χ (a • x)) = algebraMap R C (χ a) * algebraMap R C (r * χ x) := by
  simp only [smul_eq_mul, map_mul]; ring

end

/- English proof (translation)
Use `⟨finFunctionFinEquiv.symm ⟨m, h2⟩, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h push Not at h`. Use `finFunctionFinEquiv_apply (finFunctionFinEquiv.symm ⟨m, h2⟩)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Simplify using `[h] at this`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]`.
-/
theorem digits {p f m : ℕ} (h1 : 1 ≤ m) (h2 : m < p ^ f) :
    ∃ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) ∧ ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
  refine ⟨finFunctionFinEquiv.symm ⟨m, h2⟩, ?_, ?_⟩
  · by_contra h
    push Not at h
    have := finFunctionFinEquiv_apply (finFunctionFinEquiv.symm ⟨m, h2⟩)
    rw [Equiv.apply_symm_apply] at this
    simp [h] at this
    omega
  · rw [← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]

/- English proof (translation)
Use `⟨1, fun _ => δ, ⟨?_⟩, by simp⟩` and prove the remaining obligations. Conclude with `((φ.quotKerEquivOfSurjective hφ).symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans (LinearEquiv.funUnique (Fin 1) R (R ⧸ Ideal.span {δ})).symm`.
-/
theorem hasLen_quot {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) {M : Type} [AddCommGroup M] [Module R M] (φ : R →ₗ[R] M)
    (hφ : Function.Surjective φ) (δ : R) (hk : LinearMap.ker φ = Ideal.span {δ}) :
    HasLen v R M (v (algebraMap R C δ)) := by
  refine ⟨1, fun _ => δ, ⟨?_⟩, by simp⟩
  exact ((φ.quotKerEquivOfSurjective hφ).symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    (LinearEquiv.funUnique (Fin 1) R (R ⧸ Ideal.span {δ})).symm

end GlobalTheory.CompanionTheory.Ar.GR.ROm

open GlobalTheory.CompanionTheory.Ar.GR.ROm PositivityTheory.HtPt.Rb in
/- English proof (translation)
Introduce `p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hf AA hst σ hσ c hc n`. Use `haveI : IsDomain R := hv.hom_inj.isDomain`. Establish `hp2 : 2 ≤ p` using `hpp.out.two_le`. Establish `hf0 : 0 < f` using `Nat.pos_of_ne_zero (f_ne_zero hf)`. Establish `hord : orderOf σ = p ^ f - 1` using `(FundGen.main p C v R hv hp F f hf σ hσ).1`.

Take `⟨h0, -⟩` from `exists_inv_card hv hp hf`. Establish `hprin` using `eig_rank_one p C v R hv hp F f hf AA hst`. Establish `hmono` using `(GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hp F f hf AA hst σ hσ c hc).2`. Establish `hq : 1 ≤ p ^ f` using `Nat.one_le_pow _ _ (by omega)`. Establish `hsq : ∀ n, (fun a => algebraMap R C (c n ^ p * (σ ^ p ^ (n + 1)) a)) ∈ sqIdeal (augIdeal AA.carrier)` using `fun n => by`.

Use `pow_mem_sq AA (σ ^ p ^ n) (hc n ▸ Ideal.mem_span_singleton_self (c n)) hp2` as an intermediate fact. Rewrite `this` using `[← pow_mul, ← pow_succ]`. Then use the resulting hypothesis. Establish `hdvd : ∀ n, c n ^ p ∈ Ideal.span {c (n + 1)}` using `fun n => by`. Rewrite using `[← hc, mem_x_ideal_iff]`. Conclude with `sq_le AA (hsq n)`.

Establish `hper : ∀ n, σ ^ p ^ (n + f) = σ ^ p ^ n` using `fun n => by`. Rewrite using `[pow_eq_pow_iff_modEq, hord, pow_add]`. Establish `: p ^ f ≡ 1 [MOD (p ^ f - 1)]` using `((Nat.modEq_iff_dvd' hq).2 dvd_rfl).symm`. Simplify using `using this.mul_left (p ^ n)`. Establish `hcarry` using `frobeniusChain_carry p f hp2 hf0 (fun n => v (algebraMap R C (c n))) (fun n => v_eq_of_span hv (by rw [← hc, ← hc, hper])) (fun n => hv.map_le_one _) (fun n => by simpa only [map_pow] using v_le_of_mem hv (hdvd n))`.

Use `choose c' hc'0 hc' using fun m : ℕ => (hprin (σ ^ m)).1`. Establish `hdec` using `(r_decomp_relay p C v R hv hp F f hf AA hst σ hσ c' hc').1`. Establish `hiff : ∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈ sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p}`. Introduce `r`. Prove the components needed by the constructor for the conclusion.

Introduce `hr`. Rewrite `hr` using `[hdec]`. Use `sq_bound hv _ ((LinearMap.proj (R := R) (φ := fun _ : F => C) 1).comp (projL (σ ^ p ^ (n + 1)))) (v (algebraMap R C (c n)) ^ p) ?_ _ hr` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, projL_apply, proj_eigen_self h0 _ _ (eig_fun _ r)]`. Simplify using `only [LinearMap.proj_apply, map_one, mul_one] at this`.

Rewrite using `[Ideal.mem_span_singleton]`. Use `hv.dvd_of_le ?_` and prove the remaining obligations. Simplify `this` using `only [map_pow]`. Introduce and unpack `_ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩`. Simplify using `only [Finset.coe_Icc, Set.mem_Icc] at hm hm'`.

Establish `e : ((fun a : F => algebraMap R C (c' m * (σ ^ m) a)) * fun a : F => algebraMap R C (c' m' * (σ ^ m') a)) = fun a : F => algebraMap R C ((c' m * c' m') * (σ ^ (m + m')) a)`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.mul_apply, pow_add, MulChar.mul_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[LinearMap.comp_apply, projL_apply]`.

Simplify using `only []`. Rewrite using `[e]`. Distinguish the cases in `hχ : σ ^ p ^ (n + 1) = σ ^ (m + m')`. Rewrite using `[hχ, proj_eigen_self h0 _ _ (eig_fun _ _)]`. Simplify using `only [LinearMap.proj_apply, map_one, mul_one]`.

Take `⟨d, ⟨i, hi⟩, hd⟩` from `digits (p := p) (f := f) hm.1 (by omega)`. Take `⟨d', ⟨i', hi'⟩, hd'⟩` from `digits (p := p) (f := f) hm'.1 (by omega)`. Establish `e1` using `hmono d ⟨i, hi⟩`. Establish `e2` using `hmono d' ⟨i', hi'⟩`. Rewrite `e1` using `[hd, hc']`.

Rewrite `e2` using `[hd', hc']`. Rewrite using `[map_mul, map_mul, v_eq_of_span hv e1, v_eq_of_span hv e2]`. Use `hcarry (fun k => (d k : ℕ) + d' k) n ?_ ?_` as an intermediate fact. Simplify `this` using `only [pow_add, Finset.prod_mul_distrib, map_prod, map_pow]`. Rewrite using `[Finset.sum_add_distrib]`.

Establish `a1` using `Finset.single_le_sum (f := fun k => (d k : ℕ)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Establish `a2` using `Finset.single_le_sum (f := fun k => (d' k : ℕ)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i')`. Use linear arithmetic over natural numbers and integers. Simplify using `only [add_mul, Finset.sum_add_distrib, hd, hd']`. Rewrite using `[← hord, ← pow_eq_pow_iff_modEq, hχ]`.

Rewrite using `[proj_eigen_ne hχ _ (eig_fun _ _)]`. Simplify using the standard rewrite rules. Introduce `hr`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Use `Submodule.smul_mem _ s (hsq n) using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `a`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_mul, mul_assoc]`. Use `⟨hiff, ?_, fun δ hδ => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.1 (hdvd n)`. Conclude with `⟨s, hs.symm⟩`.

Establish `hne : c (n + 1) ≠ 0`. Introduce `h`. Use `hc (n + 1)` as an intermediate fact. Rewrite `this` using `[hc', h, Ideal.span_singleton_zero, Ideal.span_singleton_eq_bot]`. Conclude with `hc'0 _ this`.

Establish `hg : (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) ∈ eig AA.carrier (σ ^ p ^ (n + 1))` using `((hprin _).2 _).2 ⟨_, hc (n + 1) ▸ Ideal.mem_span_singleton_self _, rfl⟩`. Establish `hsm : ∀ r : R, r • (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) = fun a => algebraMap R C (r * c (n + 1) * (σ ^ p ^ (n + 1)) a)` using `fun r => by`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_mul, mul_assoc]`. Use `hasLen_quot v ((Submodule.mkQ _).comp (LinearMap.toSpanSingleton R _ ⟨_, hg⟩)) ?_ δ ?_` and prove the remaining obligations.

Use `(Submodule.mkQ_surjective _).comp ?_` and prove the remaining obligations. Introduce and unpack `⟨g, hg'⟩`. Take `⟨r, hr, rfl⟩` from `((hprin _).2 _).1 hg'`. Rewrite `hr` using `[hc]`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`.

Conclude with `⟨s, Subtype.ext (hsm s)⟩`. Use extensionality with `r`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `r • (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) ∈ _ ↔ _`. Rewrite using `[hsm, hiff, hδ, Ideal.mem_span_singleton, Ideal.mem_span_singleton, mul_dvd_mul_iff_right hne]`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_product : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → ∀ n, (∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈ sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p}) ∧ (∃ δ : R, c n ^ p = δ * c (n + 1)) ∧ ∀ δ : R, c n ^ p = δ * c (n + 1) → HasLen v R (OmType AA.carrier (σ ^ p ^ (n + 1))) (v (algebraMap R C δ)) := by
  intro p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hf AA hst σ hσ c hc n
  haveI : IsDomain R := hv.hom_inj.isDomain
  have hp2 : 2 ≤ p := hpp.out.two_le
  have hf0 : 0 < f := Nat.pos_of_ne_zero (f_ne_zero hf)
  have hord : orderOf σ = p ^ f - 1 := (FundGen.main p C v R hv hp F f hf σ hσ).1
  obtain ⟨h0, -⟩ := exists_inv_card hv hp hf
  have hprin := eig_rank_one p C v R hv hp F f hf AA hst
  have hmono := (GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hp F f hf AA hst σ hσ c hc).2
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ (by omega)
  have hsq : ∀ n, (fun a => algebraMap R C (c n ^ p * (σ ^ p ^ (n + 1)) a)) ∈
      sqIdeal (augIdeal AA.carrier) := fun n => by
    have := pow_mem_sq AA (σ ^ p ^ n) (hc n ▸ Ideal.mem_span_singleton_self (c n)) hp2
    rwa [← pow_mul, ← pow_succ] at this
  have hdvd : ∀ n, c n ^ p ∈ Ideal.span {c (n + 1)} := fun n => by
    rw [← hc, mem_x_ideal_iff]
    exact sq_le AA (hsq n)
  have hper : ∀ n, σ ^ p ^ (n + f) = σ ^ p ^ n := fun n => by
    rw [pow_eq_pow_iff_modEq, hord, pow_add]
    have : p ^ f ≡ 1 [MOD (p ^ f - 1)] := ((Nat.modEq_iff_dvd' hq).2 dvd_rfl).symm
    simpa using this.mul_left (p ^ n)
  have hcarry := frobeniusChain_carry p f hp2 hf0 (fun n => v (algebraMap R C (c n)))
    (fun n => v_eq_of_span hv (by rw [← hc, ← hc, hper])) (fun n => hv.map_le_one _)
    (fun n => by simpa only [map_pow] using v_le_of_mem hv (hdvd n))
  choose c' hc'0 hc' using fun m : ℕ => (hprin (σ ^ m)).1
  have hdec := (r_decomp_relay p C v R hv hp F f hf AA hst σ hσ c' hc').1
  have hiff : ∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈
      sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p} := by
    intro r
    constructor
    · intro hr
      rw [hdec] at hr
      have := sq_bound hv _ ((LinearMap.proj (R := R) (φ := fun _ : F => C) 1).comp
        (projL (σ ^ p ^ (n + 1)))) (v (algebraMap R C (c n)) ^ p) ?_ _ hr
      · rw [LinearMap.comp_apply, projL_apply, proj_eigen_self h0 _ _ (eig_fun _ r)] at this
        simp only [LinearMap.proj_apply, map_one, mul_one] at this
        rw [Ideal.mem_span_singleton]
        refine hv.dvd_of_le ?_
        simpa only [map_pow] using this
      · rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
        simp only [Finset.coe_Icc, Set.mem_Icc] at hm hm'
        have e : ((fun a : F => algebraMap R C (c' m * (σ ^ m) a)) *
            fun a : F => algebraMap R C (c' m' * (σ ^ m') a)) =
            fun a : F => algebraMap R C ((c' m * c' m') * (σ ^ (m + m')) a) := by
          funext a
          simp only [Pi.mul_apply, pow_add, MulChar.mul_apply, map_mul]; ring
        rw [LinearMap.comp_apply, projL_apply]
        simp only []
        rw [e]
        by_cases hχ : σ ^ p ^ (n + 1) = σ ^ (m + m')
        · rw [hχ, proj_eigen_self h0 _ _ (eig_fun _ _)]
          simp only [LinearMap.proj_apply, map_one, mul_one]
          obtain ⟨d, ⟨i, hi⟩, hd⟩ := digits (p := p) (f := f) hm.1 (by omega)
          obtain ⟨d', ⟨i', hi'⟩, hd'⟩ := digits (p := p) (f := f) hm'.1 (by omega)
          have e1 := hmono d ⟨i, hi⟩
          have e2 := hmono d' ⟨i', hi'⟩
          rw [hd, hc'] at e1
          rw [hd', hc'] at e2
          rw [map_mul, map_mul, v_eq_of_span hv e1, v_eq_of_span hv e2]
          have := hcarry (fun k => (d k : ℕ) + d' k) n ?_ ?_
          · simpa only [pow_add, Finset.prod_mul_distrib, map_prod, map_pow] using this
          · rw [Finset.sum_add_distrib]
            have a1 := Finset.single_le_sum (f := fun k => (d k : ℕ)) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ i)
            have a2 := Finset.single_le_sum (f := fun k => (d' k : ℕ)) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ i')
            omega
          · simp only [add_mul, Finset.sum_add_distrib, hd, hd']
            rw [← hord, ← pow_eq_pow_iff_modEq, hχ]
        · rw [proj_eigen_ne hχ _ (eig_fun _ _)]
          simp
    · intro hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      convert Submodule.smul_mem _ s (hsq n) using 1
      funext a
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, mul_assoc]
  refine ⟨hiff, ?_, fun δ hδ => ?_⟩
  · obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hdvd n)
    exact ⟨s, hs.symm⟩
  · have hne : c (n + 1) ≠ 0 := by
      intro h
      have := hc (n + 1)
      rw [hc', h, Ideal.span_singleton_zero, Ideal.span_singleton_eq_bot] at this
      exact hc'0 _ this
    have hg : (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) ∈
        eig AA.carrier (σ ^ p ^ (n + 1)) :=
      ((hprin _).2 _).2 ⟨_, hc (n + 1) ▸ Ideal.mem_span_singleton_self _, rfl⟩
    have hsm : ∀ r : R, r • (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) =
        fun a => algebraMap R C (r * c (n + 1) * (σ ^ p ^ (n + 1)) a) := fun r => by
      funext a
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, mul_assoc]
    refine hasLen_quot v ((Submodule.mkQ _).comp (LinearMap.toSpanSingleton R _ ⟨_, hg⟩)) ?_ δ ?_
    · refine (Submodule.mkQ_surjective _).comp ?_
      rintro ⟨g, hg'⟩
      obtain ⟨r, hr, rfl⟩ := ((hprin _).2 _).1 hg'
      rw [hc] at hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      exact ⟨s, Subtype.ext (hsm s)⟩
    · ext r
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      change r • (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) ∈ _ ↔ _
      rw [hsm, hiff, hδ, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        mul_dvd_mul_iff_right hne]
