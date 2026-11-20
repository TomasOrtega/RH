import Mathlib

namespace GlobalTheory.FinProjComplete

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_smul_top_pi {R ι : Type*} [CommRing R] [Finite ι] (J : Ideal R) (x : ι → R) :
    x ∈ (J • ⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := fun _ : ι => R) i) h
    rw [Submodule.map_smul''] at this
    simpa using Submodule.smul_mono le_rfl le_top this
  · have hx : x = ∑ i, x i • Pi.single i (1 : R) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the argument to an intermediate assertion. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem isAdicComplete_pi {R ι : Type*} [CommRing R] [Finite ι] (J : Ideal R)
    [IsAdicComplete J R] : IsAdicComplete J (ι → R) := by
  have hR : ∀ (x : R) n, x ≡ 0 [SMOD (J ^ n • ⊤ : Submodule R R)] ↔ x ∈ J ^ n := by
    intro x n; simp [SModEq.sub_mem]
  suffices h : IsHausdorff J (ι → R) ∧ IsPrecomplete J (ι → R) from
    have := h.1; have := h.2; {}
  refine ⟨⟨fun x hx => funext fun j => IsHausdorff.haus' (I := J) (x j) fun n => ?_⟩,
    ⟨fun u hu => ?_⟩⟩
  · rw [hR]
    have := SModEq.sub_mem.1 (hx n)
    simpa using (mem_smul_top_pi (J ^ n) _).1 this j
  · have h1 : ∀ i, ∃ L : R, ∀ k, u k i ≡ L [SMOD (J ^ k • ⊤ : Submodule R R)] :=
      fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (mem_smul_top_pi (J ^ a) _).1 (SModEq.sub_mem.1 (hu hab)) i
    choose L hL using h1
    refine ⟨L, fun k => SModEq.sub_mem.2 ((mem_smul_top_pi (J ^ k) _).2 fun i => ?_)⟩
    have := SModEq.sub_mem.1 (hL i k)
    rw [smul_eq_mul, Ideal.mul_top] at this
    simpa using this

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem map_mem_pow_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (f : M →ₗ[R] N) {x y : M} {n : ℕ}
    (h : x ≡ y [SMOD (J ^ n • ⊤ : Submodule R M)]) :
    f x ≡ f y [SMOD (J ^ n • ⊤ : Submodule R N)] := by
  rw [SModEq.sub_mem] at h ⊢
  have := Submodule.mem_map_of_mem (f := f) h
  rw [Submodule.map_smul'', map_sub] at this
  exact Submodule.smul_mono le_rfl le_top this

/- English proof (translation)
Reduce the argument to an intermediate assertion. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem isAdicComplete_of_retract {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (π : N →ₗ[R] M) (s : M →ₗ[R] N)
    (hs : ∀ x, π (s x) = x) [IsAdicComplete J N] : IsAdicComplete J M := by
  suffices h : IsHausdorff J M ∧ IsPrecomplete J M from
    have := h.1; have := h.2; {}
  refine ⟨⟨fun x hx => ?_⟩, ⟨fun u hu => ?_⟩⟩
  · have : s x = 0 := IsHausdorff.haus' (I := J) (s x) fun n => by
      simpa using map_mem_pow_smul_top J s (hx n)
    rw [← hs x, this, map_zero]
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => s (u k))
      fun hab => map_mem_pow_smul_top J s (hu hab)
    exact ⟨π L, fun n => by simpa [hs] using map_mem_pow_smul_top J π (hL n)⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isAdicComplete_span_natCast_of_finite_projective (p : ℕ) (O A : Type) [CommRing O] [CommRing A]
    [Algebra O A] [Module.Finite O A] [Module.Projective O A]
    [IsAdicComplete (Ideal.span {(p : O)}) O] : IsAdicComplete (Ideal.span {(p : A)}) A := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' O A
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have : IsAdicComplete (Ideal.span {(p : O)}) (Fin r → O) := isAdicComplete_pi _
  have hO : IsAdicComplete (Ideal.span {(p : O)}) A :=
    isAdicComplete_of_retract _ π s fun x => by simpa using LinearMap.congr_fun hs x
  have hmap : (Ideal.span {(p : O)}).map (algebraMap O A) = Ideal.span {(p : A)} := by
    simp [Ideal.map_span]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).2 hO

end GlobalTheory.FinProjComplete
