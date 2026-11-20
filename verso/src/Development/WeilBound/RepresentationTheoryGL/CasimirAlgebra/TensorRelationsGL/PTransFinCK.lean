import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

namespace PositivityTheory.Rg.Cz

namespace TF

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro z hz`. Simplify using `using hz`. Consider the case `succ k ih => intro z hz`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hZ _ (ih z hz)`.
-/
theorem pow_mem' {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (Z : Submodule ℂ U)
    (hZ : ∀ z ∈ Z, T z ∈ Z) : ∀ k : ℕ, ∀ z ∈ Z, (T ^ k) z ∈ Z := by
  intro k
  induction k with
  | zero => intro z hz; simpa using hz
  | succ k ih => intro z hz; rw [pow_succ', Module.End.mul_apply]; exact hZ _ (ih z hz)

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro w`. Simplify using the standard rewrite rules. Consider the case `succ k ih => intro w`.

Rewrite using `[pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, ← Module.End.mul_apply, ← pow_succ']`.
-/
theorem restrict_pow_coe {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (Z : Submodule ℂ U)
    (hZ : ∀ z ∈ Z, T z ∈ Z) : ∀ (k : ℕ) (w : Z), (((T.restrict hZ) ^ k) w : U) = (T ^ k) (w : U) := by
  intro k
  induction k with
  | zero => intro w; simp
  | succ k ih => intro w; rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, ← Module.End.mul_apply, ← pow_succ']

/- English proof (translation)
Take `⟨N, hN⟩` from `Filter.eventually_atTop.1 (LinearMap.eventually_isCompl_ker_pow_range_pow (T.restrict hZ))`. Establish `hc` using `hN (N + 1) (by omega)`. Establish `hmem : (⟨z0, hz0⟩ : Z) ∈ LinearMap.ker ((T.restrict hZ) ^ (N + 1)) ⊔ LinearMap.range ((T.restrict hZ) ^ (N + 1))`. Rewrite using `[hc.codisjoint.eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 hmem`. Take `⟨w, rfl⟩` from `hb`. Use `⟨N + 1, a, a.2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← restrict_pow_coe T Z hZ, LinearMap.mem_ker.1 ha]`. Both sides reduce to the same expression.

Establish `h1 : (z0 : U) = (a : U) + (T ^ (N + 1)) (w : U)`. Rewrite using `[← restrict_pow_coe T Z hZ, ← Submodule.coe_add, hab]`. Establish `h2 : e ((T ^ (N + 1)) (w : U)) = 0`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `he _ (pow_mem' T Z hZ N _ w.2)`.

Introduce `h0`. Apply `hez` to reduce the goal to its premises. Rewrite using `[h1, map_add, h0, h2, add_zero]`.
-/
theorem fit_step {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (e : U →ₗ[ℂ] ℂ)
    (Z : Submodule ℂ U) [FiniteDimensional ℂ Z] (hZ : ∀ z ∈ Z, T z ∈ Z) (he : ∀ z ∈ Z, e (T z) = 0)
    (z0 : U) (hz0 : z0 ∈ Z) (hez : e z0 ≠ 0) : ∃ N : ℕ, ∃ a ∈ Z, (T ^ N) a = 0 ∧ e a ≠ 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (LinearMap.eventually_isCompl_ker_pow_range_pow (T.restrict hZ))
  have hc := hN (N + 1) (by omega)
  have hmem : (⟨z0, hz0⟩ : Z) ∈ LinearMap.ker ((T.restrict hZ) ^ (N + 1)) ⊔
      LinearMap.range ((T.restrict hZ) ^ (N + 1)) := by
    rw [hc.codisjoint.eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨w, rfl⟩ := hb
  refine ⟨N + 1, a, a.2, ?_, ?_⟩
  · rw [← restrict_pow_coe T Z hZ, LinearMap.mem_ker.1 ha]; rfl
  · have h1 : (z0 : U) = (a : U) + (T ^ (N + 1)) (w : U) := by
      rw [← restrict_pow_coe T Z hZ, ← Submodule.coe_add, hab]
    have h2 : e ((T ^ (N + 1)) (w : U)) = 0 := by
      rw [pow_succ', Module.End.mul_apply]
      exact he _ (pow_mem' T Z hZ N _ w.2)
    intro h0
    apply hez
    rw [h1, map_add, h0, h2, add_zero]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce and unpack `Z - - - ⟨z, hz, hez⟩`. Conclude with `⟨z, hz, fun h => hez (by rw [h, map_zero]), by simp⟩`. Consider the case `@insert i0 s hi0 ih`.

Introduce and unpack `Z hfd hZ he ⟨z0, hz0, hez⟩`. Establish `hZ0` using `hZ i0 (Finset.mem_insert_self _ _)`. Take `⟨N, a, haZ, haN, hea⟩` from `fit_step (T i0) e Z hZ0 (he i0 (Finset.mem_insert_self _ _)) z0 hz0 hez`. Establish `hfd' : FiniteDimensional ℂ ↥(Z ⊓ LinearMap.ker (T i0 ^ N))` using `Submodule.finiteDimensional_of_le inf_le_left`. Take `⟨z1, hz1, hz1ne, hz1s⟩` from `ih (Z ⊓ LinearMap.ker (T i0 ^ N)) hfd' (fun i hi z hz => by`.

Use `⟨hZ i (Finset.mem_insert_of_mem hi) z hz.1, ?_⟩` and prove the remaining obligations. Establish `hk : (T i0 ^ N) z = 0` using `hz.2`. Use `show (T i0 ^ N) (T i z) = 0`. Rewrite using `[← Module.End.mul_apply, ((hT i i0).pow_right N).eq.symm, Module.End.mul_apply, hk, map_zero])`. Use the proof step `(fun i hi z hz => he i (Finset.mem_insert_of_mem hi) z hz.1) ⟨a, ⟨haZ, haN⟩, hea⟩`.

Establish `hex : ∃ k, (T i0 ^ k) z1 = 0` using `⟨N, hz1.2⟩`. Establish `hk0 : Nat.find hex ≠ 0`. Introduce `h`. Use `Nat.find_spec hex` as an intermediate fact. Rewrite `this` using `[h, pow_zero, Module.End.one_apply]`.

Conclude with `hz1ne this`. Use `⟨(T i0 ^ (Nat.find hex - 1)) z1, pow_mem' _ _ hZ0 _ _ hz1.1, Nat.find_min hex (by omega), ?_⟩` and prove the remaining obligations. Introduce `i hi`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Rewrite using `[← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]`.

Conclude with `Nat.find_spec hex`. Rewrite using `[← Module.End.mul_apply, ((hT i i0).pow_right _).eq, Module.End.mul_apply, hz1s i hi, map_zero]`.
-/
theorem common_ker {U : Type*} [AddCommGroup U] [Module ℂ U] (T : ℕ → Module.End ℂ U)
    (hT : ∀ i j, Commute (T i) (T j)) (e : U →ₗ[ℂ] ℂ) (s : Finset ℕ) :
    ∀ Z : Submodule ℂ U, FiniteDimensional ℂ Z → (∀ i ∈ s, ∀ z ∈ Z, T i z ∈ Z) →
      (∀ i ∈ s, ∀ z ∈ Z, e (T i z) = 0) → (∃ z ∈ Z, e z ≠ 0) → ∃ z ∈ Z, z ≠ 0 ∧ ∀ i ∈ s, T i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rintro Z - - - ⟨z, hz, hez⟩
    exact ⟨z, hz, fun h => hez (by rw [h, map_zero]), by simp⟩
  | @insert i0 s hi0 ih =>
    rintro Z hfd hZ he ⟨z0, hz0, hez⟩
    have hZ0 := hZ i0 (Finset.mem_insert_self _ _)
    obtain ⟨N, a, haZ, haN, hea⟩ :=
      fit_step (T i0) e Z hZ0 (he i0 (Finset.mem_insert_self _ _)) z0 hz0 hez
    have hfd' : FiniteDimensional ℂ ↥(Z ⊓ LinearMap.ker (T i0 ^ N)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨z1, hz1, hz1ne, hz1s⟩ := ih (Z ⊓ LinearMap.ker (T i0 ^ N)) hfd'
      (fun i hi z hz => by
        refine ⟨hZ i (Finset.mem_insert_of_mem hi) z hz.1, ?_⟩
        have hk : (T i0 ^ N) z = 0 := hz.2
        show (T i0 ^ N) (T i z) = 0
        rw [← Module.End.mul_apply, ((hT i i0).pow_right N).eq.symm,
          Module.End.mul_apply, hk, map_zero])
      (fun i hi z hz => he i (Finset.mem_insert_of_mem hi) z hz.1) ⟨a, ⟨haZ, haN⟩, hea⟩
    have hex : ∃ k, (T i0 ^ k) z1 = 0 := ⟨N, hz1.2⟩
    have hk0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, pow_zero, Module.End.one_apply] at this
      exact hz1ne this
    refine ⟨(T i0 ^ (Nat.find hex - 1)) z1, pow_mem' _ _ hZ0 _ _ hz1.1, Nat.find_min hex (by omega), ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
      exact Nat.find_spec hex
    · rw [← Module.End.mul_apply, ((hT i i0).pow_right _).eq, Module.End.mul_apply, hz1s i hi, map_zero]

end TF

end PositivityTheory.Rg.Cz
