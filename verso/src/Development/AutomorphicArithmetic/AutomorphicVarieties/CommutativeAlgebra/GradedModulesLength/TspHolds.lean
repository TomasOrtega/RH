import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NsPoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FtHolds

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

/- English proof (translation)
Introduce `O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW I hI σ hσ`. Use `haveI : Algebra.FiniteType (𝒜 0) A := (ft_holds O A 𝒜 x hW).1`. Set `p : A →ₗ[O] 𝒜 0` to `(DirectSum.component O ℤ (fun i => 𝒜 i) 0).comp (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap`. Establish `hpa : ∀ a : A, p a = DirectSum.decompose 𝒜 a 0` using `fun a => rfl`. Establish `pz : ∀ {i : ℤ} {u : A}, u ∈ 𝒜 i → i ≠ 0 → p u = 0`.

Introduce `i u hu hi`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hpa]`. Simplify using `using DirectSum.decompose_of_mem_ne 𝒜 hu hi`. Establish `ps : ∀ {u : A} (hu : u ∈ 𝒜 0), p u = ⟨u, hu⟩`.

Introduce `u hu`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hpa]`. Conclude with `DirectSum.decompose_of_mem_same 𝒜 hu`. Use `set J : Ideal A := I ⊔ Ideal.map (algebraMap (𝒜 0) A) (RingHom.ker σ) with hJ`.

Establish `hgen : ∀ c : 𝒜 0, σ c = 0 → ∀ a : A, σ (p (a * (c : A))) = 0`. Introduce `c hc a`. Proceed by induction on `a using DirectSum.Decomposition.inductionOn 𝒜 with`. Consider the case `zero => simp`. Consider the case `homogeneous a`.

Establish `hm : (a : A) * c ∈ 𝒜 (_ + 0)` using `SetLike.mul_mem_graded a.2 c.2`. Name the introduced variables `i`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Establish `hm' : (a : A) * c ∈ 𝒜 0` using `by simpa using hm`.

Rewrite using `[ps hm', show (⟨(a : A) * c, hm'⟩ : 𝒜 0) = ⟨a, a.2⟩ * c from rfl, map_mul, hc, mul_zero]`. Rewrite using `[pz hm (by simpa using hi), map_zero]`. Consider the case `add u v hu hv => rw [add_mul, map_add, map_add, hu, hv, add_zero]`. Establish `hJ0 : ∀ y ∈ J, σ (p y) = 0`. Introduce `y hy`.

Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.mp hy`. Use `clear hy`. Establish `h1 : σ (p u) = 0`. Apply `hσ` to reduce the goal to its premises. Rewrite using `[hpa]`.

Conclude with `hI 0 hu`. Establish `h2 : ∀ a : A, σ (p (a * v)) = 0`. Unfold `Ideal.map at hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨c, hc, rfl⟩` from `hw`. Conclude with `hgen c hc`. Consider the case `zero => simp`. Consider the case `add w w' _ _ hw hw'`. Introduce `a`.

Rewrite using `[mul_add, map_add, map_add, hw, hw', add_zero]`. Consider the case `smul a' w _ hw`. Introduce `a`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hw (a * a')`.

Establish `h3` using `h2 1`. Rewrite `h3` using `[one_mul]`. Rewrite using `[map_add, map_add, h1, h3, add_zero]`. Take `⟨ξ, hξ1, hξ2, -⟩` from `ns_holds O (𝒜 0) A K σ J 1 (fun b hb => Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb)) (by`. Introduce `b n hb hmem`.

Apply `hb` to reduce the goal to its premises. Rewrite `hmem` using `[one_pow, mul_one]`. Use `hJ0 _ hmem` as an intermediate fact. Rewrite using `[show (algebraMap (𝒜 0) A b) = (b : A) from rfl, ps b.2] at this)` and apply the resulting hypothesis. Use `⟨ξ, fun u hu => hξ2 u (Ideal.mem_sup_left hu), ?_⟩` and prove the remaining obligations.

Use extensionality with `b`. Conclude with `hξ1 b`.
-/
theorem UpperTheory.V.Alg.M.tsp_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ I : Ideal A, I.IsHomogeneous 𝒜 → ∀ σ : 𝒜 0 →ₐ[O] K, (∀ b : 𝒜 0, (b : A) ∈ I → σ b = 0) →
      ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ res0 𝒜 ξ = σ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW I hI σ hσ
  haveI : Algebra.FiniteType (𝒜 0) A := (ft_holds O A 𝒜 x hW).1
  let p : A →ₗ[O] 𝒜 0 :=
    (DirectSum.component O ℤ (fun i => 𝒜 i) 0).comp (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap
  have hpa : ∀ a : A, p a = DirectSum.decompose 𝒜 a 0 := fun a => rfl
  have pz : ∀ {i : ℤ} {u : A}, u ∈ 𝒜 i → i ≠ 0 → p u = 0 := by
    intro i u hu hi
    apply Subtype.ext
    rw [hpa]
    simpa using DirectSum.decompose_of_mem_ne 𝒜 hu hi
  have ps : ∀ {u : A} (hu : u ∈ 𝒜 0), p u = ⟨u, hu⟩ := by
    intro u hu
    apply Subtype.ext
    rw [hpa]
    exact DirectSum.decompose_of_mem_same 𝒜 hu
  set J : Ideal A := I ⊔ Ideal.map (algebraMap (𝒜 0) A) (RingHom.ker σ) with hJ
  have hgen : ∀ c : 𝒜 0, σ c = 0 → ∀ a : A, σ (p (a * (c : A))) = 0 := by
    intro c hc a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous a =>
      have hm : (a : A) * c ∈ 𝒜 (_ + 0) := SetLike.mul_mem_graded a.2 c.2
      rename_i i
      by_cases hi : i = 0
      · subst hi
        have hm' : (a : A) * c ∈ 𝒜 0 := by simpa using hm
        rw [ps hm', show (⟨(a : A) * c, hm'⟩ : 𝒜 0) = ⟨a, a.2⟩ * c from rfl, map_mul, hc, mul_zero]
      · rw [pz hm (by simpa using hi), map_zero]
    | add u v hu hv => rw [add_mul, map_add, map_add, hu, hv, add_zero]
  have hJ0 : ∀ y ∈ J, σ (p y) = 0 := by
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    clear hy
    have h1 : σ (p u) = 0 := by
      apply hσ
      rw [hpa]
      exact hI 0 hu
    have h2 : ∀ a : A, σ (p (a * v)) = 0 := by
      unfold Ideal.map at hv
      induction hv using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨c, hc, rfl⟩ := hw
        exact hgen c hc
      | zero => simp
      | add w w' _ _ hw hw' =>
        intro a
        rw [mul_add, map_add, map_add, hw, hw', add_zero]
      | smul a' w _ hw =>
        intro a
        rw [smul_eq_mul, ← mul_assoc]
        exact hw (a * a')
    have h3 := h2 1
    rw [one_mul] at h3
    rw [map_add, map_add, h1, h3, add_zero]
  obtain ⟨ξ, hξ1, hξ2, -⟩ := ns_holds O (𝒜 0) A K σ J 1
    (fun b hb => Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb))
    (by
      intro b n hb hmem
      apply hb
      rw [one_pow, mul_one] at hmem
      have := hJ0 _ hmem
      rwa [show (algebraMap (𝒜 0) A b) = (b : A) from rfl, ps b.2] at this)
  refine ⟨ξ, fun u hu => hξ2 u (Ideal.mem_sup_left hu), ?_⟩
  ext b
  exact hξ1 b
