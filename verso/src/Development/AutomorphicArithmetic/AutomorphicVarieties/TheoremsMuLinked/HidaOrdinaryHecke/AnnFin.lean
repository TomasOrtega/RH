import Mathlib

open IsLocalRing

/- English proof (translation)
Introduce `O A T M _ _ _ _ _ _ _ _ _ x μ hμ`. Use `set N : Submodule A M := (RingHom.ker x • ⊤ : Submodule A M) with hN`. Establish `hmap : ∀ (f : Module.End A M) (y : M), y ∈ N → f y ∈ N`. Introduce `f y hy`. Establish `h : N.map f ≤ N`.

Rewrite using `[hN, Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`. Conclude with `h ⟨y, hy, rfl⟩`. Set `I : Ideal T` to `{ carrier := {t | ∀ y : M, μ t y ∈ N} add_mem' := by`. Introduce `a b ha hb`.

Establish `ha' : ∀ y : M, μ a y ∈ N` using `ha`. Establish `hb' : ∀ y : M, μ b y ∈ N` using `hb`. Use `show ∀ y : M, μ (a + b) y ∈ N`. Introduce `y`. Rewrite using `[map_add, LinearMap.add_apply]`.

Conclude with `N.add_mem (ha' y) (hb' y)`. Use the proof step `zero_mem' := by show ∀ y : M, μ 0 y ∈ N`. Introduce `y`. Rewrite using `[map_zero, LinearMap.zero_apply]`. Conclude with `N.zero_mem`.

Use the proof step `smul_mem' := by`. Introduce `c t ht`. Establish `ht' : ∀ y : M, μ t y ∈ N` using `ht`. Use `show ∀ y : M, μ (c • t) y ∈ N`. Introduce `y`.

Rewrite using `[smul_eq_mul, map_mul, Module.End.mul_apply]`. Conclude with `hmap _ _ (ht' y) }`. Use `⟨I, fun t => Iff.rfl, ?_⟩` and prove the remaining obligations. Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin (R := A) (M := M)`. Use `letI : Module O M := Module.compHom M (algebraMap O A)`.

Use `haveI : IsScalarTower O A M := ⟨fun o a m => by show (o • a) • m = algebraMap O A o • (a • m)`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Set `N' : Submodule O M` to `N.restrictScalars O`. Establish `hspanA : ∀ y : M, y ∈ Submodule.span A (Set.range s)` using `fun y => hs ▸ Submodule.mem_top`. Establish `hfinQ : Module.Finite O (M ⧸ N')`.

Use `⟨(Submodule.fg_def).2 ⟨_, Set.finite_range (fun i => N'.mkQ (s i)), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `q -`. Take `⟨y, rfl⟩` from `N'.mkQ_surjective q`. Use `Submodule.span_induction ?_ ?_ ?_ ?_ (hspanA y)` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Introduce `a z _ hz`. Establish `hd : a - algebraMap O A (x a) ∈ RingHom.ker x`. Rewrite using `[RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]`.

Establish `he : N'.mkQ (a • z) = x a • N'.mkQ z`. Rewrite using `[← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.restrictScalars_mem]`. Use `show a • z - algebraMap O A (x a) • z ∈ N`. Rewrite using `[← sub_smul, hN]`. Conclude with `Submodule.smul_mem_smul hd Submodule.mem_top`.

Rewrite using `[he]`. Conclude with `Submodule.smul_mem _ _ hz`. Set `φ : T →ₗ[O] (Fin n → M ⧸ N')` to `{ toFun := fun t i => N'.mkQ (μ t (s i)) map_add' := by`. Introduce `a b`. Use function extensionality and compare the values at `i`.

Simplify using `[map_add]`. Use the proof step `map_smul' := by`. Introduce `o t`. Use function extensionality and compare the values at `i`. Simplify using `only [RingHom.id_apply, Pi.smul_apply]`.

Rewrite using `[Algebra.smul_def, map_mul, Module.End.mul_apply, hμ]`. Conclude with `N'.mkQ.map_smul o (μ t (s i)) }`. Establish `hker : LinearMap.ker φ ≤ LinearMap.ker (Ideal.Quotient.mkₐ O I).toLinearMap`. Introduce `t ht`. Rewrite `ht`, the goal using `[LinearMap.mem_ker]`.

Establish `hti : ∀ i, μ t (s i) ∈ N`. Introduce `i`. Establish `h1` using `congrFun ht i`. Express the relevant statement in the definitionally equal form `N'.mkQ (μ t (s i)) = 0 at h1`. Rewrite `h1` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem]`. Then use the resulting hypothesis.

Establish `htI : t ∈ I` using `by show ∀ y : M, μ t y ∈ N`. Introduce `y`. Use `Submodule.span_induction ?_ ?_ ?_ ?_ (hspanA y)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hti i`.

Rewrite using `[map_zero]`. Conclude with `N.zero_mem`. Introduce `a b _ _ ha hb`. Rewrite using `[map_add]`. Conclude with `N.add_mem ha hb`.

Introduce `a z _ hz`. Rewrite using `[LinearMap.map_smul]`. Conclude with `N.smul_mem a hz`. Use `show Ideal.Quotient.mkₐ O I t = 0`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `htI`. Use `haveI : Module.Finite O (LinearMap.range φ) := Module.IsNoetherian.finite O _`. Use `haveI : Module.Finite O (T ⧸ LinearMap.ker φ) := Module.Finite.equiv (φ.quotKerEquivRange).symm`. Conclude with `Module.Finite.of_surjective ((LinearMap.ker φ).liftQ _ hker) (by`. Introduce `q`.

Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Conclude with `⟨Submodule.Quotient.mk t, rfl⟩)`.
-/
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.annFin :
    ∀ {O A T M : Type} [CommRing O] [IsNoetherianRing O] [CommRing A] [Algebra O A] [CommRing T] [Algebra O T] [AddCommGroup M] [Module A M] [Module.Finite A M] (x : A →ₐ[O] O) (μ : T →+* Module.End A M), (∀ (o : O) (y : M), μ (algebraMap O T o) y = algebraMap O A o • y) → ∃ I : Ideal T, (∀ t, t ∈ I ↔ ∀ y : M, μ t y ∈ (RingHom.ker x • ⊤ : Submodule A M)) ∧ Module.Finite O (T ⧸ I) := by
  intro O A T M _ _ _ _ _ _ _ _ _ x μ hμ
  classical
  set N : Submodule A M := (RingHom.ker x • ⊤ : Submodule A M) with hN
  have hmap : ∀ (f : Module.End A M) (y : M), y ∈ N → f y ∈ N := by
    intro f y hy
    have h : N.map f ≤ N := by
      rw [hN, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h ⟨y, hy, rfl⟩
  let I : Ideal T :=
    { carrier := {t | ∀ y : M, μ t y ∈ N}
      add_mem' := by
        intro a b ha hb
        have ha' : ∀ y : M, μ a y ∈ N := ha
        have hb' : ∀ y : M, μ b y ∈ N := hb
        show ∀ y : M, μ (a + b) y ∈ N
        intro y
        rw [map_add, LinearMap.add_apply]
        exact N.add_mem (ha' y) (hb' y)
      zero_mem' := by
        show ∀ y : M, μ 0 y ∈ N
        intro y
        rw [map_zero, LinearMap.zero_apply]
        exact N.zero_mem
      smul_mem' := by
        intro c t ht
        have ht' : ∀ y : M, μ t y ∈ N := ht
        show ∀ y : M, μ (c • t) y ∈ N
        intro y
        rw [smul_eq_mul, map_mul, Module.End.mul_apply]
        exact hmap _ _ (ht' y) }
  refine ⟨I, fun t => Iff.rfl, ?_⟩
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  letI : Module O M := Module.compHom M (algebraMap O A)
  haveI : IsScalarTower O A M := ⟨fun o a m => by
    show (o • a) • m = algebraMap O A o • (a • m)
    rw [Algebra.smul_def, mul_smul]⟩
  let N' : Submodule O M := N.restrictScalars O
  have hspanA : ∀ y : M, y ∈ Submodule.span A (Set.range s) := fun y => hs ▸ Submodule.mem_top
  have hfinQ : Module.Finite O (M ⧸ N') := by
    refine ⟨(Submodule.fg_def).2 ⟨_, Set.finite_range (fun i => N'.mkQ (s i)), ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨y, rfl⟩ := N'.mkQ_surjective q
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspanA y)
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    · intro a z _ hz
      have hd : a - algebraMap O A (x a) ∈ RingHom.ker x := by
        rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
      have he : N'.mkQ (a • z) = x a • N'.mkQ z := by
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
          Submodule.restrictScalars_mem]
        show a • z - algebraMap O A (x a) • z ∈ N
        rw [← sub_smul, hN]
        exact Submodule.smul_mem_smul hd Submodule.mem_top
      rw [he]
      exact Submodule.smul_mem _ _ hz
  let φ : T →ₗ[O] (Fin n → M ⧸ N') :=
    { toFun := fun t i => N'.mkQ (μ t (s i))
      map_add' := by
        intro a b
        funext i
        simp [map_add]
      map_smul' := by
        intro o t
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [Algebra.smul_def, map_mul, Module.End.mul_apply, hμ]
        exact N'.mkQ.map_smul o (μ t (s i)) }
  have hker : LinearMap.ker φ ≤ LinearMap.ker (Ideal.Quotient.mkₐ O I).toLinearMap := by
    intro t ht
    rw [LinearMap.mem_ker] at ht ⊢
    have hti : ∀ i, μ t (s i) ∈ N := by
      intro i
      have h1 := congrFun ht i
      change N'.mkQ (μ t (s i)) = 0 at h1
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem] at h1
    have htI : t ∈ I := by
      show ∀ y : M, μ t y ∈ N
      intro y
      refine Submodule.span_induction ?_ ?_ ?_ ?_ (hspanA y)
      · rintro _ ⟨i, rfl⟩
        exact hti i
      · rw [map_zero]
        exact N.zero_mem
      · intro a b _ _ ha hb
        rw [map_add]
        exact N.add_mem ha hb
      · intro a z _ hz
        rw [LinearMap.map_smul]
        exact N.smul_mem a hz
    show Ideal.Quotient.mkₐ O I t = 0
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact htI
  haveI : Module.Finite O (LinearMap.range φ) := Module.IsNoetherian.finite O _
  haveI : Module.Finite O (T ⧸ LinearMap.ker φ) := Module.Finite.equiv (φ.quotKerEquivRange).symm
  exact Module.Finite.of_surjective ((LinearMap.ker φ).liftQ _ hker) (by
    intro q
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨Submodule.Quotient.mk t, rfl⟩)
