import Formalism.SharpRestriction.GrowthBounds.RootWeights.DeltaIntegralEnvelopingStable

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Unfold `weightSp at hnu`. Establish `hy_w : ∀ b, ρ b b y = (nu b : K) • y`. Introduce `b`. Establish `h1` using `(Submodule.mem_iInf _).mp hnu b`. Rewrite `h1` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`.

Simplify using `using h1`. Establish `R : ∀ p q s t (x : W), ρ p q (ρ s t x) = ρ s t (ρ p q x) + ((if q = s then ρ p t else 0) - (if t = p then ρ s q else 0)) x`. Introduce `p q s t x`. Establish `h` using `LinearMap.congr_fun (hρ p q s t) x`. Rewrite using `[← h, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]`.

Normalize the expressions using the abelian group laws. Establish `r1 : ∀ x, ρ a a (ρ c a x) = ρ c a (ρ a a x) - ρ c a x`. Introduce `x`. Rewrite using `[R a a c a x]`. Simplify using `[hac]`.

Apply the tactic sequence `all_goals abel`. Establish `r2 : ∀ x, ρ c c (ρ c a x) = ρ c a (ρ c c x) + ρ c a x`. Introduce `x`. Rewrite using `[R c c c a x]`. Simplify using `[hac]`.

Establish `r3 : ∀ x, ρ a c (ρ c a x) = ρ c a (ρ a c x) + ρ a a x - ρ c c x`. Introduce `x`. Rewrite using `[R a c c a x]`. Simplify using the standard rewrite rules. Apply the tactic sequence `all_goals abel`.

Establish `hA : ∀ k : ℕ, ρ a a ((ρ c a ^ k) y) = ((nu a : K) - k) • (ρ c a ^ k) y`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [hy_w a]`. Consider the case `succ k ih`.

Rewrite using `[pow_succ', Module.End.mul_apply, r1, ih, map_smul, Nat.cast_succ]`. Use `module`. Establish `hC : ∀ k : ℕ, ρ c c ((ρ c a ^ k) y) = ((nu c : K) + k) • (ρ c a ^ k) y`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp [hy_w c]`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, r2, ih, map_smul, Nat.cast_succ]`. Use `module`. Establish `hB : ∀ k : ℕ, ρ a c ((ρ c a ^ (k + 1)) y) = (((k : K) + 1) * ((nu a : K) - nu c - k)) • (ρ c a ^ k) y`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Simplify using `only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero]`. Rewrite using `[r3, he, map_zero, hy_w a, hy_w c]`.

Use `module`. Consider the case `succ k ih`. Rewrite using `[pow_succ' (ρ c a) (k + 1), Module.End.mul_apply, r3, ih, map_smul, hA (k + 1), hC (k + 1)]`. Rewrite using `[← Module.End.mul_apply (ρ c a) (ρ c a ^ k) y, ← pow_succ']`. Use `push_cast`.

Use `module`. Establish `hfin : ∃ k, (ρ c a ^ k) y = 0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hinj : Function.Injective (fun k : ℕ => (nu a : K) - k)`.

Introduce `i j hij`. Simplify using `using hij`. Use `first`. Consider the case `exact Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (nu a : K) - k) hinj (fun k => Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (hA k), hall k⟩) (Module.End.finite_hasEigenvalue (ρ a a))`. Consider the case `exact Module.Finite.not_linearIndependent_of_infinite _ (Module.End.eigenvectors_linearIndependent' (ρ a a) _ hinj _ (fun k => ⟨Module.End.mem_eigenspace_iff.mpr (hA k), hall k⟩))`.

Take `⟨k0, hk0, hmin⟩ : ∃ k0, (ρ c a ^ k0) y = 0 ∧ ∀ j < k0, (ρ c a ^ j) y ≠ 0` from `⟨Nat.find hfin, Nat.find_spec hfin, fun j hj => Nat.find_min hfin hj⟩`. Establish `hk0pos : k0 ≠ 0`. Introduce `h0`. Rewrite `hk0` using `[h0, pow_zero, Module.End.one_apply]`. Conclude with `hy hk0`.

Take `⟨m, rfl⟩ : ∃ m, k0 = m + 1` from `⟨k0 - 1, by omega⟩`. Establish `hym : (ρ c a ^ m) y ≠ 0` using `hmin m (by omega)`. Use `⟨m, ?_, hym, hk0⟩` and prove the remaining obligations. Establish `h` using `hB m`. Rewrite `h` using `[hk0, map_zero]`.

Establish `h2` using `(smul_eq_zero.mp h.symm).resolve_right hym`. Establish `hm1 : ((m : K) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero m`. Establish `h3 : (nu a : K) - nu c - m = 0` using `(mul_eq_zero.mp h2).resolve_left hm1`. Establish `h4 : ((nu a - nu c : ℤ) : K) = ((m : ℤ) : K)`. Use `push_cast`.

Take the linear combination `h3`. Conclude with `h4` after adjusting the coercions.
-/
theorem sl2_string_nonvanishing {n : ℕ} {K W : Type*} [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {ρ : GLOps n K W}
    (hρ : ∀ a b c d, ρ a b * ρ c d - ρ c d * ρ a b = (if b = c then ρ a d else 0) - (if d = a then ρ c b else 0))
    {a c : Fin n} (hac : a ≠ c) {y : W} (hy : y ≠ 0) {nu : Fin n → ℤ} (hnu : y ∈ weightSp ρ nu)
    (he : ρ a c y = 0) :
    ∃ m : ℕ, nu a - nu c = (m : ℤ) ∧ ((ρ c a) ^ m) y ≠ 0 ∧ ((ρ c a) ^ (m + 1)) y = 0 := by
  classical
  unfold weightSp at hnu
  have hy_w : ∀ b, ρ b b y = (nu b : K) • y := by
    intro b
    have h1 := (Submodule.mem_iInf _).mp hnu b
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
    simpa using h1
  have R : ∀ p q s t (x : W), ρ p q (ρ s t x) = ρ s t (ρ p q x) +
      ((if q = s then ρ p t else 0) - (if t = p then ρ s q else 0)) x := by
    intro p q s t x
    have h := LinearMap.congr_fun (hρ p q s t) x
    rw [← h, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
    abel
  have r1 : ∀ x, ρ a a (ρ c a x) = ρ c a (ρ a a x) - ρ c a x := by
    intro x
    rw [R a a c a x]
    simp [hac]
    all_goals abel
  have r2 : ∀ x, ρ c c (ρ c a x) = ρ c a (ρ c c x) + ρ c a x := by
    intro x
    rw [R c c c a x]
    simp [hac]
  have r3 : ∀ x, ρ a c (ρ c a x) = ρ c a (ρ a c x) + ρ a a x - ρ c c x := by
    intro x
    rw [R a c c a x]
    simp
    all_goals abel
  have hA : ∀ k : ℕ, ρ a a ((ρ c a ^ k) y) = ((nu a : K) - k) • (ρ c a ^ k) y := by
    intro k
    induction k with
    | zero => simp [hy_w a]
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, r1, ih, map_smul, Nat.cast_succ]
      module
  have hC : ∀ k : ℕ, ρ c c ((ρ c a ^ k) y) = ((nu c : K) + k) • (ρ c a ^ k) y := by
    intro k
    induction k with
    | zero => simp [hy_w c]
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, r2, ih, map_smul, Nat.cast_succ]
      module
  have hB : ∀ k : ℕ, ρ a c ((ρ c a ^ (k + 1)) y) =
      (((k : K) + 1) * ((nu a : K) - nu c - k)) • (ρ c a ^ k) y := by
    intro k
    induction k with
    | zero =>
      simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero]
      rw [r3, he, map_zero, hy_w a, hy_w c]
      module
    | succ k ih =>
      rw [pow_succ' (ρ c a) (k + 1), Module.End.mul_apply, r3, ih, map_smul, hA (k + 1), hC (k + 1)]
      rw [← Module.End.mul_apply (ρ c a) (ρ c a ^ k) y, ← pow_succ']
      push_cast
      module
  have hfin : ∃ k, (ρ c a ^ k) y = 0 := by
    by_contra hall
    push_neg at hall
    have hinj : Function.Injective (fun k : ℕ => (nu a : K) - k) := by
      intro i j hij
      simpa using hij
    first
    | exact Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (nu a : K) - k) hinj
        (fun k => Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.mpr (hA k), hall k⟩)
        (Module.End.finite_hasEigenvalue (ρ a a))
    | exact Module.Finite.not_linearIndependent_of_infinite _
        (Module.End.eigenvectors_linearIndependent' (ρ a a) _ hinj _
          (fun k => ⟨Module.End.mem_eigenspace_iff.mpr (hA k), hall k⟩))
  obtain ⟨k0, hk0, hmin⟩ : ∃ k0, (ρ c a ^ k0) y = 0 ∧ ∀ j < k0, (ρ c a ^ j) y ≠ 0 :=
    ⟨Nat.find hfin, Nat.find_spec hfin, fun j hj => Nat.find_min hfin hj⟩
  have hk0pos : k0 ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Module.End.one_apply] at hk0
    exact hy hk0
  obtain ⟨m, rfl⟩ : ∃ m, k0 = m + 1 := ⟨k0 - 1, by omega⟩
  have hym : (ρ c a ^ m) y ≠ 0 := hmin m (by omega)
  refine ⟨m, ?_, hym, hk0⟩
  have h := hB m
  rw [hk0, map_zero] at h
  have h2 := (smul_eq_zero.mp h.symm).resolve_right hym
  have hm1 : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have h3 : (nu a : K) - nu c - m = 0 := (mul_eq_zero.mp h2).resolve_left hm1
  have h4 : ((nu a - nu c : ℤ) : K) = ((m : ℤ) : K) := by
    push_cast
    linear_combination h3
  exact_mod_cast h4

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

/- English proof (translation)
Establish `hA` using `adjoint_end_isGLRep hI.1`. Establish `hz : ∀ a b, adjointEndAction E a b f0 = 0`. Introduce `a b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Conclude with `hf.2.2 a b h`.

Substitute `h` using the available equality. Use `mem_weightSpace_iff_diag_scalar.1 hf.2.1 a` as an intermediate fact. Simplify using `using this`. Take `⟨m, hm, -, h2⟩` from `sl2_string_nonvanishing hA.1 (ne_of_lt h) hf.1 hf.2.1 (hf.2.2 b a h)`. Establish `hm0 : m = 0` using `by simpa using hm.symm`.

Substitute `hm0` using the available equality. Simplify using `using h2`. Establish `hcomm : ∀ a b x, f0 (E a b x) = E a b (f0 x)`. Introduce `a b x`. Use `congrArg (fun T : Module.End (KK O) V => T x) (hz a b)` as an intermediate fact.

Simplify using `only [adjointEndAction_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at this`. Conclude with `(sub_eq_zero.1 this).symm`. Establish `hU : ∀ u ∈ Umon E, ∀ x, f0 (u x) = u (f0 x)`. Introduce `u hu`. Proceed by induction on `hu using Submonoid.closure_induction with`.

Consider the case `mem g hg => obtain ⟨ab, rfl⟩ := hg`. Conclude with `hcomm ab.1 ab.2`. Consider the case `one => intro x`. Both sides reduce to the same expression. Consider the case `mul a b _ _ iha ihb => intro x`.

Rewrite using `[Module.End.mul_apply, iha, ihb, Module.End.mul_apply]`. Establish `hv : f0 v ∈ weightSp E lam`. Rewrite using `[mem_weightSpace_iff_diag_scalar]`. Introduce `a`. Rewrite using `[← hcomm, mem_weightSpace_iff_diag_scalar.1 hI.2.2.1.2.1 a, map_smul]`.

Take `⟨c, hc⟩` from `irreducible_highest_weight_line hI hv`. Use `⟨c, LinearMap.ext fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : (⊤ : Submodule (KK O) V) ≤ LinearMap.eqLocus f0 (c • (1 : Module.End (KK O) V))`. Rewrite using `[← hI.2.2.2]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨u, hu, rfl⟩`. Use `show f0 (u v) = (c • (1 : Module.End (KK O) V)) (u v)`. Rewrite using `[hU u hu, hc, map_smul]`. Simplify using the standard rewrite rules. Conclude with `h1 Submodule.mem_top`.
-/
theorem weight_zero_hwv_end_scalar [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) {f0 : Module.End (KK O) V}
    (hf : IsHWV (adjointEndAction E) 0 f0) : ∃ c : KK O, f0 = c • 1 := by
  have hA := adjoint_end_isGLRep hI.1
  have hz : ∀ a b, adjointEndAction E a b f0 = 0 := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · exact hf.2.2 a b h
    · subst h
      have := mem_weightSpace_iff_diag_scalar.1 hf.2.1 a
      simpa using this
    · obtain ⟨m, hm, -, h2⟩ := sl2_string_nonvanishing hA.1 (ne_of_lt h) hf.1 hf.2.1 (hf.2.2 b a h)
      have hm0 : m = 0 := by simpa using hm.symm
      subst hm0
      simpa using h2
  have hcomm : ∀ a b x, f0 (E a b x) = E a b (f0 x) := by
    intro a b x
    have := congrArg (fun T : Module.End (KK O) V => T x) (hz a b)
    simp only [adjointEndAction_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at this
    exact (sub_eq_zero.1 this).symm
  have hU : ∀ u ∈ Umon E, ∀ x, f0 (u x) = u (f0 x) := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem g hg => obtain ⟨ab, rfl⟩ := hg; exact hcomm ab.1 ab.2
    | one => intro x; rfl
    | mul a b _ _ iha ihb => intro x; rw [Module.End.mul_apply, iha, ihb, Module.End.mul_apply]
  have hv : f0 v ∈ weightSp E lam := by
    rw [mem_weightSpace_iff_diag_scalar]; intro a
    rw [← hcomm, mem_weightSpace_iff_diag_scalar.1 hI.2.2.1.2.1 a, map_smul]
  obtain ⟨c, hc⟩ := irreducible_highest_weight_line hI hv
  refine ⟨c, LinearMap.ext fun x => ?_⟩
  have h1 : (⊤ : Submodule (KK O) V) ≤ LinearMap.eqLocus f0 (c • (1 : Module.End (KK O) V)) := by
    rw [← hI.2.2.2]
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    show f0 (u v) = (c • (1 : Module.End (KK O) V)) (u v)
    rw [hU u hu, hc, map_smul]; simp
  exact h1 Submodule.mem_top

def traceInvariantProjection (O : Type*) [CommRing O] [IsDomain O] (V : Type*) [AddCommGroup V] [Module (KK O) V] :
    Module.End (KK O) (Module.End (KK O) V) :=
  (LinearMap.trace (KK O) V).smulRight (((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V))

/- English proof (translation)
Establish `e : adjointEndAction E a b g = E a b * g - g * E a b`. Simplify using `[adjointEndAction]`. Rewrite using `[e, map_sub, LinearMap.trace_mul_comm, sub_self]`.
-/
private theorem trace_map_ring_hom_lemma [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V) (a b : Fin n)
    (g : Module.End (KK O) V) : LinearMap.trace (KK O) V (adjointEndAction E a b g) = 0 := by
  have e : adjointEndAction E a b g = E a b * g - g * E a b := by
    simp [adjointEndAction]
  rw [e, map_sub, LinearMap.trace_mul_comm, sub_self]

/- English proof (translation)
Simplify using `[adjointEndAction]`.
-/
private theorem t12_sc_lemma_2 (E : GLOps n (KK O) V) (a b : Fin n) (c : KK O) :
    adjointEndAction E a b (c • (1 : Module.End (KK O) V)) = 0 := by
  simp [adjointEndAction]

/- English proof (translation)
Establish `hU : ∀ u ∈ Umon (adjointEndAction E), u = 1 ∨ ((∀ g, LinearMap.trace (KK O) V (u g) = 0) ∧ (∀ c : KK O, u (c • 1) = 0))`. Introduce `u hu`. Unfold `Umon at hu`. Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem x hx`.

Take `⟨⟨a, b⟩, rfl⟩` from `hx`. Use `right`. Conclude with `⟨fun g => trace_map_ring_hom_lemma E a b g, fun c => t12_sc_lemma_2 E a b c⟩`. Consider the case `one => left`. Both sides reduce to the same expression.

Consider the case `mul x y _ _ hx hy`. Break down `hy with rfl | ⟨hy1, hy2⟩` into its components or cases. Rewrite using `[mul_one]`. Conclude with `hx`. Use `right`.

Break down `hx with rfl | ⟨hx1, hx2⟩` into its components or cases. Rewrite using `[one_mul]`. Conclude with `⟨hy1, hy2⟩`. Use `⟨fun g => ?_, fun c => ?_⟩` and prove the remaining obligations. Establish `e : (x * y) g = x (y g)` using `rfl`.

Rewrite using `[e]`. Conclude with `hx1 _`. Establish `e : (x * y) (c • 1) = x (y (c • 1))` using `rfl`. Rewrite using `[e, hy2 c, map_zero]`. Establish `hdim : (Module.finrank (KK O) V : KK O) ≠ 0`.

Establish `hv : v ≠ 0` using `hI.2.2.1.1`. Establish `hpos : 0 < Module.finrank (KK O) V` using `Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩`. Conclude with `Nat.cast_ne_zero.mpr hpos.ne'`. Establish `hInv : ∀ g, traceInvariantProjection O V g = (LinearMap.trace (KK O) V g * (Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V)`. Introduce `g`.

Simplify using `[traceInvariantProjection, LinearMap.smulRight_apply, smul_smul]`. Use `⟨fun x hx => ?_, fun mu hmu x hx => ?_⟩` and prove the remaining obligations. Unfold `isoSub at hx`. Use `Submodule.span_induction (p := fun x _ => traceInvariantProjection O V x = x) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `y ⟨u, hu, f, hf, rfl⟩`.

Take `⟨c, rfl⟩` from `weight_zero_hwv_end_scalar hI hf`. Break down `hU u hu with rfl | ⟨_, hu2⟩` into its components or cases. Rewrite using `[Module.End.one_apply, hInv, map_smul, LinearMap.trace_one, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hdim, mul_one]`. Rewrite using `[hu2, map_zero]`. Conclude with `map_zero _`.

Introduce `x y _ _ hx hy`. Rewrite using `[map_add, hx, hy]`. Introduce `a x _ hx`. Rewrite using `[map_smul, hx]`. Unfold `isoSub at hx`.

Use `Submodule.span_induction (p := fun x _ => traceInvariantProjection O V x = 0) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `y ⟨u, hu, f, hf, rfl⟩`. Rewrite using `[hInv]`. Break down `hU u hu with rfl | ⟨hu1, _⟩` into its components or cases. Take `⟨a, ha⟩` from `Function.ne_iff.mp hmu`.

Establish `ha' : mu a ≠ 0` using `ha`. Establish `hw` using `hf.2.1`. Unfold `weightSp at hw`. Establish `hfa : adjointEndAction E a a f = (mu a : KK O) • f`. Establish `h1` using `(Submodule.mem_iInf _).mp hw a`.

Rewrite `h1` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Simplify using `using h1`. Establish `htr : LinearMap.trace (KK O) V f = 0`. Establish `h0` using `trace_map_ring_hom_lemma E a a f`. Rewrite `h0` using `[hfa, map_smul, smul_eq_mul]`.

Establish `hmu0 : (mu a : KK O) ≠ 0` using `Int.cast_ne_zero.mpr ha'`. Conclude with `(mul_eq_zero.mp h0).resolve_left hmu0`. Rewrite using `[Module.End.one_apply, htr, zero_mul, zero_smul]`. Rewrite using `[hu1, zero_mul, zero_smul]`. Conclude with `map_zero _`.

Introduce `x y _ _ hx hy`. Rewrite using `[map_add, hx, hy, add_zero]`. Introduce `a x _ hx`. Rewrite using `[map_smul, hx, smul_zero]`.
-/
theorem trace_projection_isInvProj [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) : IsInvProj (adjointEndAction E) (traceInvariantProjection O V) := by
  have hU : ∀ u ∈ Umon (adjointEndAction E), u = 1 ∨
      ((∀ g, LinearMap.trace (KK O) V (u g) = 0) ∧ (∀ c : KK O, u (c • 1) = 0)) := by
    intro u hu
    unfold Umon at hu
    induction hu using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      right
      exact ⟨fun g => trace_map_ring_hom_lemma E a b g, fun c => t12_sc_lemma_2 E a b c⟩
    | one => left; rfl
    | mul x y _ _ hx hy =>
      rcases hy with rfl | ⟨hy1, hy2⟩
      · rw [mul_one]
        exact hx
      · right
        rcases hx with rfl | ⟨hx1, hx2⟩
        · rw [one_mul]
          exact ⟨hy1, hy2⟩
        · refine ⟨fun g => ?_, fun c => ?_⟩
          · have e : (x * y) g = x (y g) := rfl
            rw [e]
            exact hx1 _
          · have e : (x * y) (c • 1) = x (y (c • 1)) := rfl
            rw [e, hy2 c, map_zero]
  have hdim : (Module.finrank (KK O) V : KK O) ≠ 0 := by
    have hv : v ≠ 0 := hI.2.2.1.1
    have hpos : 0 < Module.finrank (KK O) V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩
    exact Nat.cast_ne_zero.mpr hpos.ne'
  have hInv : ∀ g, traceInvariantProjection O V g =
      (LinearMap.trace (KK O) V g * (Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V) := by
    intro g
    simp [traceInvariantProjection, LinearMap.smulRight_apply, smul_smul]
  refine ⟨fun x hx => ?_, fun mu hmu x hx => ?_⟩
  · unfold isoSub at hx
    refine Submodule.span_induction (p := fun x _ => traceInvariantProjection O V x = x) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨u, hu, f, hf, rfl⟩
      obtain ⟨c, rfl⟩ := weight_zero_hwv_end_scalar hI hf
      rcases hU u hu with rfl | ⟨_, hu2⟩
      · rw [Module.End.one_apply, hInv, map_smul, LinearMap.trace_one, smul_eq_mul, mul_assoc,
          mul_inv_cancel₀ hdim, mul_one]
      · rw [hu2, map_zero]
    · exact map_zero _
    · intro x y _ _ hx hy
      rw [map_add, hx, hy]
    · intro a x _ hx
      rw [map_smul, hx]
  · unfold isoSub at hx
    refine Submodule.span_induction (p := fun x _ => traceInvariantProjection O V x = 0) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨u, hu, f, hf, rfl⟩
      rw [hInv]
      rcases hU u hu with rfl | ⟨hu1, _⟩
      · obtain ⟨a, ha⟩ := Function.ne_iff.mp hmu
        have ha' : mu a ≠ 0 := ha
        have hw := hf.2.1
        unfold weightSp at hw
        have hfa : adjointEndAction E a a f = (mu a : KK O) • f := by
          have h1 := (Submodule.mem_iInf _).mp hw a
          rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
          simpa using h1
        have htr : LinearMap.trace (KK O) V f = 0 := by
          have h0 := trace_map_ring_hom_lemma E a a f
          rw [hfa, map_smul, smul_eq_mul] at h0
          have hmu0 : (mu a : KK O) ≠ 0 := Int.cast_ne_zero.mpr ha'
          exact (mul_eq_zero.mp h0).resolve_left hmu0
        rw [Module.End.one_apply, htr, zero_mul, zero_smul]
      · rw [hu1, zero_mul, zero_smul]
    · exact map_zero _
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro a x _ hx
      rw [map_smul, hx, smul_zero]

end hw

end Formalism.MainNotions.G.GLWeightTheory
