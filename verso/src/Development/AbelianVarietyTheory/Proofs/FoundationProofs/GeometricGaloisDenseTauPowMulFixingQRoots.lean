import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

noncomputable section

namespace GlobalTheory.K5.Dense

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

/- English proof (translation)
Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `σ hσ`. Use `⟨(fun τ => σ⁻¹ * τ) ⁻¹' (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)), ?_, (stabilizer_isOpen_of_isIntegral x).preimage (by fun_prop), ?_⟩` and prove the remaining obligations. Introduce `τ hτ`. Establish `h : σ.symm (τ x) = x` using `hτ`.

Establish `h' : τ x = σ x` using `by rw [← σ.symm_apply_eq.1 h]`. Simplify `hσ` using `[h']`. Simplify using the standard rewrite rules.
-/
theorem isClosed_eval_mem {K : Type*} [Field K] [Algebra K Ω] [Algebra.IsIntegral K Ω]
    (x : Ω) (s : Set Ω) : IsClosed {σ : Ω ≃ₐ[K] Ω | σ x ∈ s} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)), ?_,
    (stabilizer_isOpen_of_isIntegral x).preimage (by fun_prop), ?_⟩
  · intro τ hτ
    have h : σ.symm (τ x) = x := hτ
    have h' : τ x = σ x := by rw [← σ.symm_apply_eq.1 h]
    simpa [h'] using hσ
  · simp

/- English proof (translation)
Set `K` to `FractionRing (O0 p)`. Use `letI : Algebra K Ω := (IsFractionRing.lift h.inj).toAlgebra`. Establish `hK : ∀ a : O0 p, algebraMap K Ω (algebraMap (O0 p) K a) = algebraMap (O0 p) Ω a` using `fun a => IsFractionRing.lift_algebraMap h.inj a`. Use `haveI : IsScalarTower (O0 p) K Ω := IsScalarTower.of_algebraMap_eq (fun a => (hK a).symm)`. Use `haveI : IsAlgClosed Ω := h.clo`.

Use `haveI : Algebra.IsAlgebraic (O0 p) Ω := h.alg`. Use `haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) K)`. Use `haveI : IsAlgClosure K Ω := ⟨h.clo, inferInstance⟩`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap h.inj`. Use `haveI : CharZero K := RingHom.charZero (algebraMap K Ω)`.

Use `haveI : IsGalois K Ω := {}`. Establish `hfix : ∀ σ : Gal p Ω, ∀ y : K, σ (algebraMap K Ω y) = algebraMap K Ω y`. Introduce `σ y`. Establish `e : ((σ : Ω →+* Ω).comp (algebraMap K Ω)) = algebraMap K Ω`. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (O0 p))` to reduce the goal to its premises.

Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, hK]`. Conclude with `σ.commutes a`. Conclude with `congrArg (fun f : K →+* Ω => f y) e`. Set `φ : Gal p Ω → (Ω ≃ₐ[K] Ω)` to `fun σ => AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (hfix σ)`.

Establish `hφ : ∀ σ x, φ σ x = σ x` using `fun _ _ => rfl`. Set `G : ℕ → Set (Ω ≃ₐ[K] Ω)` to `fun n => {τ | ∀ m ≤ n, ∀ x, τ x ∈ P m x}`. Establish `hcl : ∀ n, IsClosed (G n)` using `fun n => by`. Establish `e : G n = ⋂ m, ⋂ (_ : m ≤ n), ⋂ x, {τ : Ω ≃ₐ[K] Ω | τ x ∈ P m x}`. Use extensionality with `τ`.

Simplify using `[G]`. Rewrite using `[e]`. Conclude with `isClosed_iInter fun m => isClosed_iInter fun _ => isClosed_iInter fun x => isClosed_eval_mem x _`. Establish `hdec : ∀ n, G (n + 1) ⊆ G n` using `fun n τ hτ m hm x => hτ m (hm.trans n.le_succ) x`. Establish `hne : ∀ n, (G n).Nonempty` using `fun n => by`.

Take `⟨σ, hσ⟩` from `hP n`. Conclude with `⟨φ σ, fun m hm x => by rw [hφ]; exact hσ m hm x⟩`. Take `⟨τ, hτ⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed G hdec hne (hcl 0).isCompact hcl`. Rewrite `hτ` using `[Set.mem_iInter]`. Conclude with `⟨τ.restrictScalars (O0 p), fun n x => hτ n n le_rfl x⟩`.
-/
theorem exists_of_seq (h : IsClo p Ω) (P : ℕ → Ω → Set Ω)
    (hP : ∀ n, ∃ σ : Gal p Ω, ∀ m ≤ n, ∀ x, σ x ∈ P m x) :
    ∃ σ : Gal p Ω, ∀ n x, σ x ∈ P n x := by
  classical
  let K := FractionRing (O0 p)
  letI : Algebra K Ω := (IsFractionRing.lift h.inj).toAlgebra
  have hK : ∀ a : O0 p, algebraMap K Ω (algebraMap (O0 p) K a) = algebraMap (O0 p) Ω a :=
    fun a => IsFractionRing.lift_algebraMap h.inj a
  haveI : IsScalarTower (O0 p) K Ω := IsScalarTower.of_algebraMap_eq (fun a => (hK a).symm)
  haveI : IsAlgClosed Ω := h.clo
  haveI : Algebra.IsAlgebraic (O0 p) Ω := h.alg
  haveI : Algebra.IsAlgebraic K Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) K)
  haveI : IsAlgClosure K Ω := ⟨h.clo, inferInstance⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap h.inj
  haveI : CharZero K := RingHom.charZero (algebraMap K Ω)
  haveI : IsGalois K Ω := {}
  have hfix : ∀ σ : Gal p Ω, ∀ y : K, σ (algebraMap K Ω y) = algebraMap K Ω y := by
    intro σ y
    have e : ((σ : Ω →+* Ω).comp (algebraMap K Ω)) = algebraMap K Ω := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (O0 p))
      ext a
      simp only [RingHom.comp_apply, hK]
      exact σ.commutes a
    exact congrArg (fun f : K →+* Ω => f y) e
  let φ : Gal p Ω → (Ω ≃ₐ[K] Ω) := fun σ => AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (hfix σ)
  have hφ : ∀ σ x, φ σ x = σ x := fun _ _ => rfl
  let G : ℕ → Set (Ω ≃ₐ[K] Ω) := fun n => {τ | ∀ m ≤ n, ∀ x, τ x ∈ P m x}
  have hcl : ∀ n, IsClosed (G n) := fun n => by
    have e : G n = ⋂ m, ⋂ (_ : m ≤ n), ⋂ x, {τ : Ω ≃ₐ[K] Ω | τ x ∈ P m x} := by
      ext τ; simp [G]
    rw [e]
    exact isClosed_iInter fun m => isClosed_iInter fun _ => isClosed_iInter fun x =>
      isClosed_eval_mem x _
  have hdec : ∀ n, G (n + 1) ⊆ G n := fun n τ hτ m hm x => hτ m (hm.trans n.le_succ) x
  have hne : ∀ n, (G n).Nonempty := fun n => by
    obtain ⟨σ, hσ⟩ := hP n
    exact ⟨φ σ, fun m hm x => by rw [hφ]; exact hσ m hm x⟩
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed G hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hτ
  exact ⟨τ.restrictScalars (O0 p), fun n x => hτ n n le_rfl x⟩

/- English proof (translation)
Take `⟨P, hP0, hPx⟩` from `h.alg.isAlgebraic x`. Use `⟨(P.aroots Ω).toFinset, fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.mem_toFinset, mem_aroots']`. Use `⟨(Polynomial.map_ne_zero_iff h.inj).2 hP0, ?_⟩` and prove the remaining obligations. Establish `e` using `Polynomial.aeval_algHom_apply (σ : Ω →ₐ[O0 p] Ω) x P`.

Simplify using `only [AlgEquiv.coe_algHom] at e`. Rewrite using `[e, hPx, map_zero]`.
-/
theorem exists_finset_orbit (h : IsClo p Ω) (x : Ω) : ∃ R : Finset Ω, ∀ σ : Gal p Ω, σ x ∈ R := by
  classical
  obtain ⟨P, hP0, hPx⟩ := h.alg.isAlgebraic x
  refine ⟨(P.aroots Ω).toFinset, fun σ => ?_⟩
  rw [Multiset.mem_toFinset, mem_aroots']
  refine ⟨(Polynomial.map_ne_zero_iff h.inj).2 hP0, ?_⟩
  have e := Polynomial.aeval_algHom_apply (σ : Ω →ₐ[O0 p] Ω) x P
  simp only [AlgEquiv.coe_algHom] at e
  rw [e, hPx, map_zero]

/- English proof (translation)
Use `⟨X ^ (p ^ n) - C 1, X_pow_sub_C_ne_zero (pow_pos hp.out.pos n) 1, ?_⟩` and prove the remaining obligations. Simplify using `[(T.prim n).pow_eq_one]`.
-/
theorem isAlgZp_zeta (T : Tower p Ω) (n : ℕ) : IsAlgZp p (T.ζ n) := by
  refine ⟨X ^ (p ^ n) - C 1, X_pow_sub_C_ne_zero (pow_pos hp.out.pos n) 1, ?_⟩
  simp [(T.prim n).pow_eq_one]

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le h`. Simplify using `only [Nat.add_sub_cancel_left]`. Use `clear h`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih => rw [← add_assoc, pow_succ', pow_mul, T.qpow, ih]`.
-/
theorem qq_pow_sub (T : Tower p Ω) {n m : ℕ} (h : n ≤ m) : T.qq m ^ p ^ (m - n) = T.qq n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]
  clear h
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, T.qpow, ih]

/- English proof (translation)
The claim follows from `hg x hx`.
-/
theorem ggeo_apply {g : Gal p Ω} (hg : g ∈ Ggeo p Ω) {x : Ω} (hx : IsAlgZp p x) : g x = x := hg x hx

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ s ih`. Rewrite using `[pow_succ, AlgEquiv.mul_apply, hτq, map_mul, ih, ggeo_apply ((Ggeo p Ω).pow_mem hτ s) (isAlgZp_zeta T n), pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tau_pow_qq (T : Tower p Ω) {τ : Gal p Ω} (hτ : τ ∈ Ggeo p Ω)
    (hτq : ∀ n, τ (T.qq n) = T.ζ n * T.qq n) (n s : ℕ) :
    (τ ^ s) (T.qq n) = T.ζ n ^ s * T.qq n := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, AlgEquiv.mul_apply, hτq, map_mul, ih,
      ggeo_apply ((Ggeo p Ω).pow_mem hτ s) (isAlgZp_zeta T n), pow_succ]
    ring

/- English proof (translation)
Introduce `g hg S`. Establish `hs : ∀ n, ∃ s : ℕ, (τ ^ s) (T.qq n) = g (T.qq n)`. Introduce `n`. Establish `hq0` using `Basic.qq_ne_zero T n`. Establish `hqp : T.qq n ^ p ^ n ≠ 0` using `pow_ne_zero _ hq0`.

Establish `e : (g (T.qq n) / T.qq n) ^ (p ^ n) = 1`. Rewrite using `[div_pow, ← map_pow, Basic.qq_pow, AlgEquiv.commutes, ← Basic.qq_pow T n, div_self hqp]`. Take `⟨i, -, hi⟩` from `(T.prim n).eq_pow_of_pow_eq_one e`. Conclude with `⟨i, by rw [tau_pow_qq T hτ hτq, hi, div_mul_cancel₀ _ hq0]⟩`. Use `choose s hs using hs`.

Set `σ : ℕ → Gal p Ω` to `fun n => (τ ^ s n)⁻¹ * g`. Establish `hσG : ∀ n, σ n ∈ Ggeo p Ω` using `fun n => (Ggeo p Ω).mul_mem ((Ggeo p Ω).inv_mem ((Ggeo p Ω).pow_mem hτ _)) hg`. Establish `hσq : ∀ n, σ n (T.qq n) = T.qq n`. Introduce `n`. Use `show ((τ ^ s n)⁻¹ * g) (T.qq n) = T.qq n`.

Rewrite using `[AlgEquiv.mul_apply, ← hs n, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]`. Use `choose R hR using fun x => exists_finset_orbit hΩ x`. Set `F : ℕ → ((x : S) → ↥(R x.1))` to `fun n x => ⟨σ n x, hR x.1 (σ n)⟩`. Take `⟨y, hy⟩` from `Finite.exists_infinite_fiber F`. Establish `hinf : (F ⁻¹' {y}).Infinite` using `Set.infinite_coe_iff.1 hy`.

Take `⟨n₁, hn₁⟩` from `hinf.nonempty`. Establish `hS : ∀ m ∈ F ⁻¹' {y}, ∀ x ∈ S, σ m x = σ n₁ x`. Introduce `m hm x hx`. Establish `e : F m = F n₁` using `(Set.mem_preimage.1 hm).trans (Set.mem_preimage.1 hn₁).symm`. Conclude with `congrArg Subtype.val (congrFun e ⟨x, hx⟩)`.

Set `P : ℕ → Ω → Set Ω` to `fun n x => {z | (IsAlgZp p x → z = x) ∧ (x ∈ S → z = σ n₁ x) ∧ (x = T.qq n → z = x)}`. Establish `hP : ∀ n, ∃ ρ : Gal p Ω, ∀ m ≤ n, ∀ x, ρ x ∈ P m x`. Introduce `n`. Take `⟨m, hm, hnm⟩` from `hinf.exists_gt n`. Use `⟨σ m, fun m' hm' x => ⟨fun hx => ggeo_apply (hσG m) hx, fun hx => hS m hm x hx, ?_⟩⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Rewrite using `[← qq_pow_sub T (hm'.trans hnm.le), map_pow, hσq m]`. Take `⟨z, hz⟩` from `exists_of_seq hΩ P hP`. Use `⟨s n₁, z, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `Subgroup.mem_inf.2 ⟨fun x hx => (hz 0 x).1 hx, Subgroup.mem_iInf.2 fun n => ?_⟩` and prove the remaining obligations.

Conclude with `(Basic.mem_gn T n z).2 ⟨(hz 0 _).1 (isAlgZp_zeta T n), (hz n _).2.2 rfl⟩`. Rewrite using `[AlgEquiv.mul_apply, (hz 0 x).2.1 hx] show (τ ^ s n₁) (((τ ^ s n₁)⁻¹ * g) x) = g x`. Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]`.
-/
theorem dense_tau_pow_mul (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (Ω : Type) [Field Ω]
    [Algebra (O0 p) Ω] (hΩ : IsClo p Ω) (T : Tower p Ω) (τ : Gal p Ω) (hτ : τ ∈ Ggeo p Ω)
    (hτq : ∀ n, τ (T.qq n) = T.ζ n * T.qq n) :
    ∀ g ∈ Ggeo p Ω, ∀ S : Finset Ω, ∃ s : ℕ, ∃ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n,
      ∀ x ∈ S, (τ ^ s * h) x = g x := by
  classical
  intro g hg S
  have hs : ∀ n, ∃ s : ℕ, (τ ^ s) (T.qq n) = g (T.qq n) := by
    intro n
    have hq0 := Basic.qq_ne_zero T n
    have hqp : T.qq n ^ p ^ n ≠ 0 := pow_ne_zero _ hq0
    have e : (g (T.qq n) / T.qq n) ^ (p ^ n) = 1 := by
      rw [div_pow, ← map_pow, Basic.qq_pow, AlgEquiv.commutes, ← Basic.qq_pow T n, div_self hqp]
    obtain ⟨i, -, hi⟩ := (T.prim n).eq_pow_of_pow_eq_one e
    exact ⟨i, by rw [tau_pow_qq T hτ hτq, hi, div_mul_cancel₀ _ hq0]⟩
  choose s hs using hs
  let σ : ℕ → Gal p Ω := fun n => (τ ^ s n)⁻¹ * g
  have hσG : ∀ n, σ n ∈ Ggeo p Ω := fun n =>
    (Ggeo p Ω).mul_mem ((Ggeo p Ω).inv_mem ((Ggeo p Ω).pow_mem hτ _)) hg
  have hσq : ∀ n, σ n (T.qq n) = T.qq n := by
    intro n
    show ((τ ^ s n)⁻¹ * g) (T.qq n) = T.qq n
    rw [AlgEquiv.mul_apply, ← hs n, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  choose R hR using fun x => exists_finset_orbit hΩ x
  let F : ℕ → ((x : S) → ↥(R x.1)) := fun n x => ⟨σ n x, hR x.1 (σ n)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber F
  have hinf : (F ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  obtain ⟨n₁, hn₁⟩ := hinf.nonempty
  have hS : ∀ m ∈ F ⁻¹' {y}, ∀ x ∈ S, σ m x = σ n₁ x := by
    intro m hm x hx
    have e : F m = F n₁ := (Set.mem_preimage.1 hm).trans (Set.mem_preimage.1 hn₁).symm
    exact congrArg Subtype.val (congrFun e ⟨x, hx⟩)
  let P : ℕ → Ω → Set Ω := fun n x =>
    {z | (IsAlgZp p x → z = x) ∧ (x ∈ S → z = σ n₁ x) ∧ (x = T.qq n → z = x)}
  have hP : ∀ n, ∃ ρ : Gal p Ω, ∀ m ≤ n, ∀ x, ρ x ∈ P m x := by
    intro n
    obtain ⟨m, hm, hnm⟩ := hinf.exists_gt n
    refine ⟨σ m, fun m' hm' x => ⟨fun hx => ggeo_apply (hσG m) hx, fun hx => hS m hm x hx, ?_⟩⟩
    rintro rfl
    rw [← qq_pow_sub T (hm'.trans hnm.le), map_pow, hσq m]
  obtain ⟨z, hz⟩ := exists_of_seq hΩ P hP
  refine ⟨s n₁, z, ?_, fun x hx => ?_⟩
  · refine Subgroup.mem_inf.2 ⟨fun x hx => (hz 0 x).1 hx, Subgroup.mem_iInf.2 fun n => ?_⟩
    exact (Basic.mem_gn T n z).2 ⟨(hz 0 _).1 (isAlgZp_zeta T n), (hz n _).2.2 rfl⟩
  · rw [AlgEquiv.mul_apply, (hz 0 x).2.1 hx]
    show (τ ^ s n₁) (((τ ^ s n₁)⁻¹ * g) x) = g x
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

end GlobalTheory.K5.Dense
