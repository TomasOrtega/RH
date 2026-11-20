import Mathlib

open TensorProduct in
/- English proof (translation)
Introduce `O B M _ _ _ _ _ _ _ x hx`. Use `set p : Ideal B := RingHom.ker x with hp`. Use `haveI hpp : p.IsPrime := RingHom.ker_isPrime x`. Establish `hs : (⟨p, hpp⟩ : PrimeSpectrum B) ∈ Module.support B M` using `Module.mem_support_iff_of_finite.mpr hx`. Establish `hnt : Nontrivial (p.ResidueField ⊗[B] M)` using `(Module.mem_support_iff_nontrivial_residueField_tensorProduct (⟨p, hpp⟩ : PrimeSpectrum B)).mp hs`.

Take `⟨v, hv⟩` from `exists_ne (0 : p.ResidueField ⊗[B] M)`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_ne_zero p.ResidueField hv`. Set `g : M →ₗ[B] p.ResidueField` to `(f.restrictScalars B) ∘ₗ (TensorProduct.mk B p.ResidueField M 1)`. Establish `hg : ∃ m₀, g m₀ ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Apply `hf` to reduce the goal to its premises. Establish `: ∀ w, f w = 0`. Introduce `w`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp [ha, hb]`. Consider the case `tmul k m`. Establish `h1 : k ⊗ₜ[B] m = k • ((1 : p.ResidueField) ⊗ₜ[B] m)`. Simplify using `[TensorProduct.smul_tmul']`.

Establish `h2 : f ((1 : p.ResidueField) ⊗ₜ[B] m) = 0` using `h m`. Rewrite using `[h1, map_smul, h2, smul_zero]`. Conclude with `this v`. Take `⟨m₀, hm₀⟩` from `hg`. Take `⟨S, hS⟩` from `Module.Finite.fg_top (R := B) (M := M)`.

Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (B ⧸ p)) S (fun m => g m)`. Set `i : (B ⧸ p) →ₗ[B] p.ResidueField` to `(IsScalarTower.toAlgHom B (B ⧸ p) p.ResidueField).toLinearMap`. Establish `hi : Function.Injective i` using `IsFractionRing.injective (B ⧸ p) p.ResidueField`. Set `c : p.ResidueField` to `algebraMap (B ⧸ p) p.ResidueField b`. Establish `hc : c ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`.

Set `g' : M →ₗ[B] p.ResidueField` to `c • g`. Establish `hr : ∀ m, g' m ∈ LinearMap.range i`. Introduce `m`. Establish `hm : m ∈ Submodule.span B (S : Set M)` using `hS ▸ Submodule.mem_top`. Establish `: Submodule.span B (S : Set M) ≤ (LinearMap.range i).comap g'`.

Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Take `⟨z, hz⟩` from `hb y hy`. Use `⟨z, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap _ _ z = c * g y`.

Rewrite using `[hz, Algebra.smul_def]`. Conclude with `this hm`. Set `h : M →ₗ[B] (B ⧸ p)` to `LinearMap.codRestrictOfInjective g' i hi hr`. Establish `hh : ∀ m, i (h m) = g' m` using `fun m => LinearMap.codRestrictOfInjective_comp_apply g' i hi hr m`. Set `e : (B ⧸ p) →+* O` to `RingHom.kerLift (x : B →+* O)`.

Establish `he : Function.Injective e` using `RingHom.kerLift_injective (x : B →+* O)`. Use `⟨e.toAddMonoidHom.comp h.toAddMonoidHom, m₀, ?_, ?_⟩` and prove the remaining obligations. Introduce `a m`. Express the relevant statement in the definitionally equal form `e (h (a • m)) = x a * e (h m)`. Rewrite using `[map_smul, Algebra.smul_def, map_mul]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `e (h m₀) ≠ 0`. Introduce `h0`. Establish `h1 : h m₀ = 0` using `he (by rw [h0, map_zero])`. Establish `h2` using `hh m₀`.

Rewrite `h2` using `[h1, map_zero]`. Conclude with `mul_ne_zero hc hm₀ h2.symm`.
-/
theorem UpperTheory.Reformulated.B.Qf1.lam0 :
    ∀ (O B M : Type) [inst : CommRing O] [IsDomain O] [inst_2 : CommRing B] [inst_3 : Algebra O B]
    [inst_4 : AddCommGroup M] [inst_5 : _root_.Module B M] [Module.Finite B M] (x : B →ₐ[O] O),
    Module.annihilator B M ≤ RingHom.ker x →
      ∃ (lam : M →+ O) (m₀ : M),
        (∀ (a : B) (m : M), (lam : M → O) (a • m) = (x : B → O) a * (lam : M → O) m) ∧ (lam : M → O) m₀ ≠ (0 : O) := by
  intro O B M _ _ _ _ _ _ _ x hx
  classical
  set p : Ideal B := RingHom.ker x with hp
  haveI hpp : p.IsPrime := RingHom.ker_isPrime x
  have hs : (⟨p, hpp⟩ : PrimeSpectrum B) ∈ Module.support B M :=
    Module.mem_support_iff_of_finite.mpr hx
  have hnt : Nontrivial (p.ResidueField ⊗[B] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct (⟨p, hpp⟩ : PrimeSpectrum B)).mp hs
  obtain ⟨v, hv⟩ := exists_ne (0 : p.ResidueField ⊗[B] M)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero p.ResidueField hv
  let g : M →ₗ[B] p.ResidueField :=
    (f.restrictScalars B) ∘ₗ (TensorProduct.mk B p.ResidueField M 1)
  have hg : ∃ m₀, g m₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    have : ∀ w, f w = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp [ha, hb]
      | tmul k m =>
        have h1 : k ⊗ₜ[B] m = k • ((1 : p.ResidueField) ⊗ₜ[B] m) := by
          simp [TensorProduct.smul_tmul']
        have h2 : f ((1 : p.ResidueField) ⊗ₜ[B] m) = 0 := h m
        rw [h1, map_smul, h2, smul_zero]
    exact this v
  obtain ⟨m₀, hm₀⟩ := hg
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := M)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (B ⧸ p)) S
    (fun m => g m)
  let i : (B ⧸ p) →ₗ[B] p.ResidueField := (IsScalarTower.toAlgHom B (B ⧸ p) p.ResidueField).toLinearMap
  have hi : Function.Injective i := IsFractionRing.injective (B ⧸ p) p.ResidueField
  let c : p.ResidueField := algebraMap (B ⧸ p) p.ResidueField b
  have hc : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  let g' : M →ₗ[B] p.ResidueField := c • g
  have hr : ∀ m, g' m ∈ LinearMap.range i := by
    intro m
    have hm : m ∈ Submodule.span B (S : Set M) := hS ▸ Submodule.mem_top
    have : Submodule.span B (S : Set M) ≤ (LinearMap.range i).comap g' := by
      rw [Submodule.span_le]
      intro y hy
      obtain ⟨z, hz⟩ := hb y hy
      refine ⟨z, ?_⟩
      change algebraMap _ _ z = c * g y
      rw [hz, Algebra.smul_def]
    exact this hm
  let h : M →ₗ[B] (B ⧸ p) := LinearMap.codRestrictOfInjective g' i hi hr
  have hh : ∀ m, i (h m) = g' m := fun m =>
    LinearMap.codRestrictOfInjective_comp_apply g' i hi hr m
  let e : (B ⧸ p) →+* O := RingHom.kerLift (x : B →+* O)
  have he : Function.Injective e := RingHom.kerLift_injective (x : B →+* O)
  refine ⟨e.toAddMonoidHom.comp h.toAddMonoidHom, m₀, ?_, ?_⟩
  · intro a m
    change e (h (a • m)) = x a * e (h m)
    rw [map_smul, Algebra.smul_def, map_mul]
    rfl
  · change e (h m₀) ≠ 0
    intro h0
    have h1 : h m₀ = 0 := he (by rw [h0, map_zero])
    have h2 := hh m₀
    rw [h1, map_zero] at h2
    exact mul_ne_zero hc hm₀ h2.symm
