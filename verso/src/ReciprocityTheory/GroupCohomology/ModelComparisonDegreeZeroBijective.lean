import ReciprocityTheory.GroupCohomology.MemZpowersQuot
import ReciprocityTheory.GroupCohomology.FiniteLevel

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def stab (M : TRep R G) (m : M.V) : Subgroup G where
  carrier := {a | M.rho a m = m}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
The claim follows from `Subgroup.isOpen_of_mem_nhds _ (FiniteLevelCohomology.stab_mem_nhds M m)`.
-/
theorem stab_isOpen (M : TRep R G) [DiscreteTopology M.V] (m : M.V) : IsOpen (stab M m : Set G) :=
  Subgroup.isOpen_of_mem_nhds _ (FiniteLevelCohomology.stab_mem_nhds M m)

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]`.
-/
theorem rho_comm (M : TRep R G) (hc : ∀ a b : G, a * b = b * a) (a b : G) (x : M.V) :
    M.rho a (M.rho b x) = M.rho b (M.rho a x) := by
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]

/- English proof (translation)
Establish `hcont : Continuous fun a : G => M.rho a m` using `M.cont.comp (f := fun a : G => (a, m)) (continuous_id.prodMk continuous_const)`. Establish `hcl : IsClosed {a : G | c a = M.rho a m - m}` using `isClosed_eq hc.1 (hcont.sub continuous_const)`. Establish `step : ∀ a : G, c (a * s) - (M.rho (a * s) m - m) = c a - (M.rho a m - m)`. Introduce `a`. Rewrite using `[hc.2, hm, map_mul, Module.End.mul_apply]`.

Simplify using `only [map_sub]`. Normalize the expressions using the abelian group laws. Establish `hz : ∀ i : ℤ, c (s ^ i) = M.rho (s ^ i) m - m`. Establish `h0 : c (s ^ (0 : ℤ)) - (M.rho (s ^ (0 : ℤ)) m - m) = 0`. Establish `e` using `hc.2 1 1`.

Simplify using `only [mul_one, map_one, Module.End.one_apply] at e`. Simplify using `only [zpow_zero, map_one, Module.End.one_apply, sub_self, sub_zero]`. Conclude with `(add_eq_left.1 e.symm)`. Introduce `i`. Establish `: c (s ^ i) - (M.rho (s ^ i) m - m) = 0`.

Proceed by induction on `i using Int.induction_on with`. Consider the case `zero => exact h0`. Consider the case `succ i ih => rw [zpow_add_one, step, ih]`. Consider the case `pred i ih => rw [← ih, ← step, zpow_sub_one, inv_mul_cancel_right]`. Conclude with `sub_eq_zero.1 this`.

Establish `hsub : (Subgroup.zpowers s : Set G) ⊆ {a : G | c a = M.rho a m - m}`. Introduce `x hx`. Take `⟨i, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hx`. Conclude with `hz i`. Establish `h` using `hcl.closure_subset_iff.2 hsub`.

Rewrite `h` using `[hs.closure_eq]`. Conclude with `h (Set.mem_univ g)`.
-/
theorem cocycle_eq_of_apply (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hs : Dense (Subgroup.zpowers s : Set G)) (c : G → M.V) (hc : c ∈ Z1 M.rho) (m : M.V)
    (hm : c s = M.rho s m - m) (g : G) : c g = M.rho g m - m := by
  have hcont : Continuous fun a : G => M.rho a m :=
    M.cont.comp (f := fun a : G => (a, m)) (continuous_id.prodMk continuous_const)
  have hcl : IsClosed {a : G | c a = M.rho a m - m} :=
    isClosed_eq hc.1 (hcont.sub continuous_const)
  have step : ∀ a : G, c (a * s) - (M.rho (a * s) m - m) = c a - (M.rho a m - m) := by
    intro a
    rw [hc.2, hm, map_mul, Module.End.mul_apply]
    simp only [map_sub]; abel
  have hz : ∀ i : ℤ, c (s ^ i) = M.rho (s ^ i) m - m := by
    have h0 : c (s ^ (0 : ℤ)) - (M.rho (s ^ (0 : ℤ)) m - m) = 0 := by
      have e := hc.2 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at e
      simp only [zpow_zero, map_one, Module.End.one_apply, sub_self, sub_zero]
      exact (add_eq_left.1 e.symm)
    intro i
    have : c (s ^ i) - (M.rho (s ^ i) m - m) = 0 := by
      induction i using Int.induction_on with
      | zero => exact h0
      | succ i ih => rw [zpow_add_one, step, ih]
      | pred i ih => rw [← ih, ← step, zpow_sub_one, inv_mul_cancel_right]
    exact sub_eq_zero.1 this
  have hsub : (Subgroup.zpowers s : Set G) ⊆ {a : G | c a = M.rho a m - m} := by
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact hz i
  have h := hcl.closure_subset_iff.2 hsub
  rw [hs.closure_eq] at h
  exact h (Set.mem_univ g)

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def psum (M : TRep R G) (s : G) (m : M.V) (j : ℕ) : M.V :=
  ∑ i ∈ Finset.range j, M.rho (s ^ i) m

/- English proof (translation)
Simplify using `only [psum, Finset.sum_range_add, map_sum, pow_add, map_mul, Module.End.mul_apply]`.
-/
theorem psum_add (M : TRep R G) (s : G) (m : M.V) (i j : ℕ) :
    psum M s m (i + j) = psum M s m i + M.rho (s ^ i) (psum M s m j) := by
  simp only [psum, Finset.sum_range_add, map_sum, pow_add, map_mul, Module.End.mul_apply]

/- English proof (translation)
Take `⟨k, hk0, hkm⟩` from `hk`. Use `set V := stab M m`. Establish `hVo` using `stab_isOpen M m`. Use `set a := V.index`. Establish `ha : 0 < a` using `index_pos hc hVo`.

Establish `hsa : s ^ a ∈ V`. Use `(zpow_mem_iff hc hs hVo (a : ℤ)).2 dvd_rfl` as an intermediate fact. Simplify using `using this`. Take `⟨W0, hW0o, hW0i⟩` from `hidx (a * k) (Nat.mul_pos ha hk0)`. Use `set W := V ⊓ W0`.

Establish `hWo : IsOpen (W : Set G)` using `hVo.inter hW0o`. Establish `hWV : W ≤ V` using `inf_le_left`. Establish `hdvd : a * k ∣ W.index` using `hW0i ▸ Subgroup.index_dvd_of_le inf_le_right`. Establish `hfixV : ∀ v ∈ V, ∀ j, M.rho v (psum M s m j) = psum M s m j`. Introduce `v hv j`.

Simplify using `only [psum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[rho_comm M hc]`. Rewrite using `[show M.rho v m = m from hv]`. Establish `hmul : ∀ t, psum M s m (a * t) = t • psum M s m a`.

Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => simp [psum]`. Consider the case `succ t ih`. Rewrite using `[Nat.mul_succ, psum_add, ih, hfixV _ (by rw [pow_mul]; exact V.pow_mem hsa t), succ_nsmul]`.

Establish `hN : psum M s m (a * k) = 0`. Rewrite using `[hmul, psum, Finset.smul_sum]`. Simplify using `only [← map_nsmul, hkm, map_zero, Finset.sum_const_zero]`. Establish `hperN : ∀ j, psum M s m (j + a * k) = psum M s m j`. Introduce `j`.

Rewrite using `[psum_add, hN, map_zero, add_zero]`. Establish `hper : ∀ j, psum M s m (j + W.index) = psum M s m j`. Take `⟨t, ht⟩` from `hdvd`. Introduce `j`. Rewrite using `[ht]`.

Conclude with `per_mul _ _ hperN j t`. Establish `hex` using `exists_pow hc hs hWo`. Use `⟨desc W hex (psum M s m), ⟨desc_continuous hc hs hWo hex _ hper, fun g h => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hg` using `Classical.choose_spec (hex g)`. Establish `hh` using `Classical.choose_spec (hex h)`.

Use `set i := Classical.choose (hex g)`. Use `set j := Classical.choose (hex h)`. Establish `hgh : (g * h)⁻¹ * s ^ (i + j) ∈ W`. Establish `e : (g * h)⁻¹ * s ^ (i + j) = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_inv_rev, pow_add]`. Use `group`. Use `_ = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by rw [hc h⁻¹ (g⁻¹ * s ^ i), mul_assoc]`. Rewrite using `[e]`. Conclude with `W.mul_mem hg hh`.

Establish `e1 : desc W hex (psum M s m) (g * h) = psum M s m (i + j)` using `desc_eq hc hs hWo hex _ hper hgh`. Establish `e2 : desc W hex (psum M s m) g = psum M s m i` using `rfl`. Establish `e3 : desc W hex (psum M s m) h = psum M s m j` using `rfl`. Rewrite using `[e1, e2, e3, psum_add]`. Use `congr 1`.

Establish `hgeq : g = s ^ i * (g⁻¹ * s ^ i)⁻¹` using `by group`. Use `conv_rhs => rw [hgeq, map_mul, Module.End.mul_apply]`. Rewrite using `[hfixV _ (hWV (W.inv_mem hg))]`. Establish `: desc W hex (psum M s m) s = psum M s m 1` using `desc_eq hc hs hWo hex _ hper (by simp)`. Rewrite using `[this]`.

Simplify using `[psum]`.
-/
theorem exists_cocycle [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (m : M.V) (hk : ∃ k : ℕ, 0 < k ∧ k • m = 0) : ∃ c ∈ Z1 M.rho, c s = m := by
  obtain ⟨k, hk0, hkm⟩ := hk
  set V := stab M m
  have hVo := stab_isOpen M m
  set a := V.index
  have ha : 0 < a := index_pos hc hVo
  have hsa : s ^ a ∈ V := by
    have := (zpow_mem_iff hc hs hVo (a : ℤ)).2 dvd_rfl
    simpa using this
  obtain ⟨W0, hW0o, hW0i⟩ := hidx (a * k) (Nat.mul_pos ha hk0)
  set W := V ⊓ W0
  have hWo : IsOpen (W : Set G) := hVo.inter hW0o
  have hWV : W ≤ V := inf_le_left
  have hdvd : a * k ∣ W.index := hW0i ▸ Subgroup.index_dvd_of_le inf_le_right

  have hfixV : ∀ v ∈ V, ∀ j, M.rho v (psum M s m j) = psum M s m j := by
    intro v hv j
    simp only [psum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rho_comm M hc]
    rw [show M.rho v m = m from hv]
  have hmul : ∀ t, psum M s m (a * t) = t • psum M s m a := by
    intro t
    induction t with
    | zero => simp [psum]
    | succ t ih =>
      rw [Nat.mul_succ, psum_add, ih, hfixV _ (by rw [pow_mul]; exact V.pow_mem hsa t), succ_nsmul]
  have hN : psum M s m (a * k) = 0 := by
    rw [hmul, psum, Finset.smul_sum]
    simp only [← map_nsmul, hkm, map_zero, Finset.sum_const_zero]
  have hperN : ∀ j, psum M s m (j + a * k) = psum M s m j := by
    intro j; rw [psum_add, hN, map_zero, add_zero]
  have hper : ∀ j, psum M s m (j + W.index) = psum M s m j := by
    obtain ⟨t, ht⟩ := hdvd
    intro j; rw [ht]; exact per_mul _ _ hperN j t
  have hex := exists_pow hc hs hWo
  refine ⟨desc W hex (psum M s m), ⟨desc_continuous hc hs hWo hex _ hper, fun g h => ?_⟩, ?_⟩
  · have hg := Classical.choose_spec (hex g)
    have hh := Classical.choose_spec (hex h)
    set i := Classical.choose (hex g)
    set j := Classical.choose (hex h)
    have hgh : (g * h)⁻¹ * s ^ (i + j) ∈ W := by
      have e : (g * h)⁻¹ * s ^ (i + j) = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by
        calc (g * h)⁻¹ * s ^ (i + j) = h⁻¹ * (g⁻¹ * s ^ i) * s ^ j := by
              rw [mul_inv_rev, pow_add]; group
          _ = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by rw [hc h⁻¹ (g⁻¹ * s ^ i), mul_assoc]
      rw [e]; exact W.mul_mem hg hh
    have e1 : desc W hex (psum M s m) (g * h) = psum M s m (i + j) := desc_eq hc hs hWo hex _ hper hgh
    have e2 : desc W hex (psum M s m) g = psum M s m i := rfl
    have e3 : desc W hex (psum M s m) h = psum M s m j := rfl
    rw [e1, e2, e3, psum_add]
    congr 1
    have hgeq : g = s ^ i * (g⁻¹ * s ^ i)⁻¹ := by group
    conv_rhs => rw [hgeq, map_mul, Module.End.mul_apply]
    rw [hfixV _ (hWV (W.inv_mem hg))]
  · have : desc W hex (psum M s m) s = psum M s m 1 :=
      desc_eq hc hs hWo hex _ hper (by simp)
    rw [this]; simp [psum]

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Use `set P := LinearMap.range (M.rho s - LinearMap.id)`. Set `f : Z1 M.rho →ₗ[R] M.V ⧸ P` to `P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 M.rho).subtype)`. Establish `hf : ∀ c : Z1 M.rho, f c = Submodule.Quotient.mk (c.1 s)` using `fun c => rfl`. Establish `hker : (B1 M.rho).comap (Z1 M.rho).subtype ≤ LinearMap.ker f`. Introduce `c hc'`.

Take `⟨m, hm⟩` from `(mem_coboundaries1 _ _).1 hc'`. Rewrite using `[LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨m, by simpa using (hm s).symm⟩`. Set `φ` to `((B1 M.rho).comap (Z1 M.rho).subtype).liftQ f hker`. Establish `hφ : ∀ c : Z1 M.rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s)` using `fun c => rfl`.

Establish `hinj : Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[hφ, Submodule.Quotient.mk_eq_zero]`.

Take `⟨m, hm⟩` from `hx`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]`. Use `⟨m, cocycle_eq_of_apply M hs c.1 c.2 m ?_⟩` and prove the remaining obligations. Rewrite using `[← hm]`. Simplify using the standard rewrite rules.

Establish `hsurj : Surjective φ`. Introduce `y`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨c, hcZ, hcs⟩` from `exists_cocycle M hc hs hidx m (htor m)`. Conclude with `⟨Submodule.Quotient.mk ⟨c, hcZ⟩, by rw [hφ]; simp [hcs]⟩`.

Conclude with `⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun c => hφ c⟩`.
-/
theorem model_comparison_degree_zero_bijective [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∃ e : H1 M.rho ≃ₗ[R] M.V ⧸ LinearMap.range (M.rho s - LinearMap.id),
      ∀ c : Z1 M.rho, e (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) := by
  set P := LinearMap.range (M.rho s - LinearMap.id)
  let f : Z1 M.rho →ₗ[R] M.V ⧸ P := P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 M.rho).subtype)
  have hf : ∀ c : Z1 M.rho, f c = Submodule.Quotient.mk (c.1 s) := fun c => rfl
  have hker : (B1 M.rho).comap (Z1 M.rho).subtype ≤ LinearMap.ker f := by
    intro c hc'
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hc'
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simpa using (hm s).symm⟩
  let φ := ((B1 M.rho).comap (Z1 M.rho).subtype).liftQ f hker
  have hφ : ∀ c : Z1 M.rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) :=
    fun c => rfl
  have hinj : Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hφ, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨m, hm⟩ := hx
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    refine ⟨m, cocycle_eq_of_apply M hs c.1 c.2 m ?_⟩
    rw [← hm]; simp
  have hsurj : Surjective φ := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨c, hcZ, hcs⟩ := exists_cocycle M hc hs hidx m (htor m)
    exact ⟨Submodule.Quotient.mk ⟨c, hcZ⟩, by rw [hφ]; simp [hcs]⟩
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun c => hφ c⟩

end ProcyclicCohomology

end ReciprocityTheory.Coh
