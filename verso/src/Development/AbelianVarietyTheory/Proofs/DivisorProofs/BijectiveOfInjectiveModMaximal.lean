import Mathlib

open scoped TensorProduct

namespace GlobalTheory.ProjBij

/- English proof (translation)
Rewrite using `[← Submodule.annihilator_eq_top_iff]`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨r, hr, hr0⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m K hK (h m hm)`. Establish `h1 : r ∈ m` using `hle (Submodule.mem_annihilator.2 hr0)`.

Apply `hm.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Use `m.sub_mem h1 hr` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_bot_of_forall_le_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K : Submodule R M) (hK : K.FG) (h : ∀ m : Ideal R, m.IsMaximal → K ≤ m • K) : K = ⊥ := by
  rw [← Submodule.annihilator_eq_top_iff]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m K hK (h m hm)
  have h1 : r ∈ m := hle (Submodule.mem_annihilator.2 hr0)
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  have := m.sub_mem h1 hr
  simpa using this

/- English proof (translation)
Rewrite using `[← (TensorProduct.quotTensorEquivQuotSMul M m).map_eq_zero_iff, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]`.
-/
theorem one_tmul_eq_zero_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (x : M) :
    ((1 : R ⧸ m) ⊗ₜ[R] x : (R ⧸ m) ⊗[R] M) = 0 ↔ x ∈ m • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M m).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

/- English proof (translation)
The claim follows from `TensorProduct.mk_surjective R M (R ⧸ m) Ideal.Quotient.mk_surjective y`.
-/
theorem exists_one_tmul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (y : (R ⧸ m) ⊗[R] M) : ∃ x : M, (1 : R ⧸ m) ⊗ₜ[R] x = y :=
  TensorProduct.mk_surjective R M (R ⧸ m) Ideal.Quotient.mk_surjective y

/- English proof (translation)
Establish `hsurj : Function.Surjective f`. Establish `key : (⊤ : Submodule R (N ⧸ LinearMap.range f)) = ⊥`. Apply `eq_bot_of_forall_le_smul _ Module.Finite.fg_top` to reduce the goal to its premises. Introduce `m hm y _`. Use `letI := Ideal.Quotient.field m`.

Establish `hi : Function.Injective (f.baseChange (R ⧸ m))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Take `⟨x, rfl⟩` from `exists_one_tmul m z`. Rewrite `hz` using `[LinearMap.baseChange_tmul, one_tmul_eq_zero_iff]`.

Conclude with `(one_tmul_eq_zero_iff m x).2 (hinj m hm x hz)`. Establish `hs` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hrk m hm)).1 hi`. Take `⟨n, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨z, hz⟩` from `hs (1 ⊗ₜ n)`. Take `⟨x, rfl⟩` from `exists_one_tmul m z`.

Rewrite `hz` using `[LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub, one_tmul_eq_zero_iff]`. Establish `h2` using `Submodule.mem_map_of_mem (f := (LinearMap.range f).mkQ) hz`. Rewrite `h2` using `[Submodule.map_smul'']`. Establish `h3` using `Submodule.smul_mono (le_refl m) le_top h2`. Establish `h4 : (LinearMap.range f).mkQ (f x) = 0` using `(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self f x)`.

Rewrite `h3` using `[map_sub, h4, zero_sub]`. Conclude with `(Submodule.neg_mem_iff _).1 h3`. Introduce `n`. Establish `: (Submodule.Quotient.mk n : N ⧸ LinearMap.range f) ∈ (⊥ : Submodule R _)`. Rewrite using `[← key]`.

Discharge the goal by the elementary cases of `trivial`. Rewrite `this` using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`. Conclude with `this`. Use `⟨?_, hsurj⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `Module.projective_lifting_property f LinearMap.id hsurj`.

Establish `hs' : ∀ n, f (s n) = n` using `fun n => LinearMap.congr_fun hs n`. Set `p : M →ₗ[R] M` to `LinearMap.id - s ∘ₗ f`. Establish `hp : Submodule.map p ⊤ = LinearMap.ker f`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, -, rfl⟩`.

Simplify using `[p, hs']`. Introduce `x hx`. Conclude with `⟨x, trivial, by simp [p, LinearMap.mem_ker.1 hx]⟩`. Rewrite using `[← LinearMap.ker_eq_bot]`. Apply `eq_bot_of_forall_le_smul` to reduce the goal to its premises.

Rewrite using `[← hp]`. Conclude with `Module.Finite.fg_top.map p`. Introduce `m hm x hx`. Establish `hx0 : f x = 0` using `hx`. Establish `h1` using `hinj m hm x (by rw [hx0]; exact Submodule.zero_mem _)`.

Establish `h2` using `Submodule.mem_map_of_mem (f := p) h1`. Rewrite `h2` using `[Submodule.map_smul'', hp]`. Simplify `h2` using `[p, hx0]`.
-/
theorem bijective_of_injective_mod_maximal
    (R M N : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hinj : ∀ m : Ideal R, m.IsMaximal → ∀ x, f x ∈ m • (⊤ : Submodule R N) →
      x ∈ m • (⊤ : Submodule R M)) :
    Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    have key : (⊤ : Submodule R (N ⧸ LinearMap.range f)) = ⊥ := by
      apply eq_bot_of_forall_le_smul _ Module.Finite.fg_top
      intro m hm y _
      letI := Ideal.Quotient.field m
      have hi : Function.Injective (f.baseChange (R ⧸ m)) := by
        rw [injective_iff_map_eq_zero]
        intro z hz
        obtain ⟨x, rfl⟩ := exists_one_tmul m z
        rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hz
        exact (one_tmul_eq_zero_iff m x).2 (hinj m hm x hz)
      have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hrk m hm)).1 hi
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨z, hz⟩ := hs (1 ⊗ₜ n)
      obtain ⟨x, rfl⟩ := exists_one_tmul m z
      rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub,
        one_tmul_eq_zero_iff] at hz
      have h2 := Submodule.mem_map_of_mem (f := (LinearMap.range f).mkQ) hz
      rw [Submodule.map_smul''] at h2
      have h3 := Submodule.smul_mono (le_refl m) le_top h2
      have h4 : (LinearMap.range f).mkQ (f x) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self f x)
      rw [map_sub, h4, zero_sub] at h3
      exact (Submodule.neg_mem_iff _).1 h3
    intro n
    have : (Submodule.Quotient.mk n : N ⧸ LinearMap.range f) ∈ (⊥ : Submodule R _) := by
      rw [← key]; trivial
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at this
    exact this
  refine ⟨?_, hsurj⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have hs' : ∀ n, f (s n) = n := fun n => LinearMap.congr_fun hs n
  let p : M →ₗ[R] M := LinearMap.id - s ∘ₗ f
  have hp : Submodule.map p ⊤ = LinearMap.ker f := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      simp [p, hs']
    · intro x hx
      exact ⟨x, trivial, by simp [p, LinearMap.mem_ker.1 hx]⟩
  rw [← LinearMap.ker_eq_bot]
  apply eq_bot_of_forall_le_smul
  · rw [← hp]; exact Module.Finite.fg_top.map p
  · intro m hm x hx
    have hx0 : f x = 0 := hx
    have h1 := hinj m hm x (by rw [hx0]; exact Submodule.zero_mem _)
    have h2 := Submodule.mem_map_of_mem (f := p) h1
    rw [Submodule.map_smul'', hp] at h2
    simpa [p, hx0] using h2

end GlobalTheory.ProjBij
