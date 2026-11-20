import Mathlib

namespace Formalism.L2.Pj.QAt.TieLDB

open Module

variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]

/- English proof (translation)
Rewrite using `[← smul_assoc, Algebra.smul_def, mul_comm, mul_smul, algebraMap_smul]`.
-/
theorem smul_comm' (s : A) (o : Localization.AtPrime p) (v : V) : s • (o • v) = o • (s • v) := by
  rw [← smul_assoc, Algebra.smul_def, mul_comm, mul_smul, algebraMap_smul]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hy⟩`. Consider the case `zero => exact ⟨1, p.primeCompl.one_mem, by rw [smul_zero]; exact G.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs, hsx⟩` from `hx`.

Take `⟨t, ht, hty⟩` from `hy`. Use `⟨s * t, p.primeCompl.mul_mem hs ht, ?_⟩` and prove the remaining obligations. Establish `e1 : (s * t) • x = t • (s • x)` using `by rw [mul_comm, mul_smul]`. Establish `e2 : (s * t) • y = s • (t • y)` using `by rw [mul_smul]`. Rewrite using `[smul_add, e1, e2]`.

Conclude with `add_mem (G.smul_mem t hsx) (G.smul_mem s hty)`. Consider the case `smul o x _ hx`. Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨⟨a, s'⟩, hos⟩` from `IsLocalization.mk'_surjective p.primeCompl o`. Use `⟨s' * s, p.primeCompl.mul_mem s'.2 hs, ?_⟩` and prove the remaining obligations.

Establish `h1 : (s' : A) • o = algebraMap A (Localization.AtPrime p) a`. Rewrite using `[← hos, Algebra.smul_def, mul_comm, IsLocalization.mk'_spec]`. Rewrite using `[mul_smul, smul_comm' p s o x, ← smul_assoc, h1, algebraMap_smul]`. Conclude with `G.smul_mem a hsx`.
-/
theorem exists_smul_mem (G : Submodule A V) {x : V}
    (hx : x ∈ Submodule.span (Localization.AtPrime p) (G : Set V)) :
    ∃ s ∈ p.primeCompl, s • x ∈ G := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, p.primeCompl.one_mem, by rw [smul_zero]; exact G.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, p.primeCompl.mul_mem hs ht, ?_⟩
    have e1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    have e2 : (s * t) • y = s • (t • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact add_mem (G.smul_mem t hsx) (G.smul_mem s hty)
  | smul o x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨a, s'⟩, hos⟩ := IsLocalization.mk'_surjective p.primeCompl o
    refine ⟨s' * s, p.primeCompl.mul_mem s'.2 hs, ?_⟩
    have h1 : (s' : A) • o = algebraMap A (Localization.AtPrime p) a := by
      rw [← hos, Algebra.smul_def, mul_comm, IsLocalization.mk'_spec]
    rw [mul_smul, smul_comm' p s o x, ← smul_assoc, h1, algebraMap_smul]
    exact G.smul_mem a hsx

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Conclude with `⟨Submodule.subset_span hx.1, hx.2⟩`. Introduce and unpack `x ⟨hxM, hxW⟩`.

Take `⟨s, hs, hsx⟩` from `exists_smul_mem p M hxM`. Establish `hu` using `IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)`. Establish `hmem : s • x ∈ Submodule.span (Localization.AtPrime p) ((M ⊓ W.restrictScalars A : Submodule A V) : Set V)` using `Submodule.subset_span ⟨hsx, W.smul_of_tower_mem s hxW⟩`. Establish `hx : x = hu.unit⁻¹ • (s • x)`. Rewrite using `[← algebraMap_smul (Localization.AtPrime p) s x]`.

Express the relevant statement in the definitionally equal form `x = hu.unit⁻¹ • (hu.unit • x)`. Rewrite using `[inv_smul_smul]`. Rewrite using `[hx]`. Conclude with `Submodule.smul_of_tower_mem _ _ hmem`.
-/
theorem span_inf_eq (M : Submodule A V) (W : Submodule (Localization.AtPrime p) V) :
    Submodule.span (Localization.AtPrime p) ((M ⊓ W.restrictScalars A : Submodule A V) : Set V) =
      Submodule.span (Localization.AtPrime p) (M : Set V) ⊓ W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact ⟨Submodule.subset_span hx.1, hx.2⟩
  · rintro x ⟨hxM, hxW⟩
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p M hxM
    have hu := IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
    have hmem : s • x ∈ Submodule.span (Localization.AtPrime p)
        ((M ⊓ W.restrictScalars A : Submodule A V) : Set V) :=
      Submodule.subset_span ⟨hsx, W.smul_of_tower_mem s hxW⟩
    have hx : x = hu.unit⁻¹ • (s • x) := by
      rw [← algebraMap_smul (Localization.AtPrime p) s x]
      change x = hu.unit⁻¹ • (hu.unit • x)
      rw [inv_smul_smul]
    rw [hx]
    exact Submodule.smul_of_tower_mem _ _ hmem

variable (H G : Submodule A V)

def inc : H →ₗ[A] Submodule.span (Localization.AtPrime p) (H : Set V) where
  toFun h := ⟨h, Submodule.subset_span h.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def locMap :
    H ⧸ G.comap H.subtype →ₗ[A] ↥(Submodule.span (Localization.AtPrime p) (H : Set V)) ⧸
      (Submodule.span (Localization.AtPrime p) (G : Set V)).comap
        (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype :=
  (G.comap H.subtype).liftQ
    (((((Submodule.span (Localization.AtPrime p) (G : Set V)).comap
      (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype).mkQ).restrictScalars A) ∘ₗ
        inc p H) (by
      intro h hh
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span hh)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem locMap_mk (h : H) :
    locMap p H G (Submodule.Quotient.mk h) = Submodule.Quotient.mk (inc p H h) := rfl

/- English proof (translation)
Rewrite using `[Module.End.isUnit_iff]`. Establish `hu` using `IsLocalization.map_units (Localization.AtPrime p) s`. Prove the components needed by the constructor for the conclusion. Introduce `z1 z2 h`. Rewrite `h` using `[Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← algebraMap_smul (Localization.AtPrime p) (s : A) z1, ← algebraMap_smul (Localization.AtPrime p) (s : A) z2]`.

Conclude with `hu.smul_left_cancel.1 h`. Introduce `z`. Use `⟨hu.unit⁻¹ • z, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.algebraMap_end_apply, ← algebraMap_smul (Localization.AtPrime p) (s : A)]`. Express the relevant statement in the definitionally equal form `hu.unit • hu.unit⁻¹ • z = z`.

Rewrite using `[smul_inv_smul]`. Use `surj y := by`. Take `⟨⟨x, hx⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨s, hs, hsx⟩` from `exists_smul_mem p H hx`. Use `⟨(Submodule.Quotient.mk ⟨s • x, hsx⟩, ⟨s, hs⟩), ?_⟩` and prove the remaining obligations.

Rewrite using `[locMap_mk]`. Both sides reduce to the same expression. Use `exists_of_eq {x₁ x₂} h := by`. Take `⟨h1, rfl⟩` from `Submodule.Quotient.mk_surjective _ x₁`. Take `⟨h2, rfl⟩` from `Submodule.Quotient.mk_surjective _ x₂`.

Rewrite `h` using `[locMap_mk, locMap_mk, Submodule.Quotient.eq]`. Establish `h' : (h1 : V) - h2 ∈ Submodule.span (Localization.AtPrime p) (G : Set V)` using `h`. Take `⟨s, hs, hsx⟩` from `exists_smul_mem p G h'`. Use `⟨⟨s, hs⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`.

Express the relevant statement in the definitionally equal form `(s • (h1 : V)) - s • (h2 : V) ∈ G`. Rewrite using `[← smul_sub]`. Conclude with `hsx`.
-/
theorem isLocalizedModule : IsLocalizedModule p.primeCompl (locMap p H G) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hu := IsLocalization.map_units (Localization.AtPrime p) s
    constructor
    · intro z1 z2 h
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        ← algebraMap_smul (Localization.AtPrime p) (s : A) z1,
        ← algebraMap_smul (Localization.AtPrime p) (s : A) z2] at h
      exact hu.smul_left_cancel.1 h
    · intro z
      refine ⟨hu.unit⁻¹ • z, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul (Localization.AtPrime p) (s : A)]
      change hu.unit • hu.unit⁻¹ • z = z
      rw [smul_inv_smul]
  surj y := by
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p H hx
    refine ⟨(Submodule.Quotient.mk ⟨s • x, hsx⟩, ⟨s, hs⟩), ?_⟩
    rw [locMap_mk]
    rfl
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨h1, rfl⟩ := Submodule.Quotient.mk_surjective _ x₁
    obtain ⟨h2, rfl⟩ := Submodule.Quotient.mk_surjective _ x₂
    rw [locMap_mk, locMap_mk, Submodule.Quotient.eq] at h
    have h' : (h1 : V) - h2 ∈ Submodule.span (Localization.AtPrime p) (G : Set V) := h
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p G h'
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    change (s • (h1 : V)) - s • (h2 : V) ∈ G
    rw [← smul_sub]
    exact hsx

/- English proof (translation)
Use `isLocalizedModule p H G` as an intermediate fact. Establish `: IsLocalizedModule p.primeCompl (locMap p H G ∘ₗ e.toLinearMap)` using `inferInstance`. Conclude with `((IsLocalizedModule.iso p.primeCompl (locMap p H G ∘ₗ e.toLinearMap)).extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)).length_eq`.
-/
theorem length_localized_eq {P : Type*} [AddCommGroup P] [Module A P]
    (e : P ≃ₗ[A] H ⧸ G.comap H.subtype) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl P) =
      Module.length (Localization.AtPrime p)
        (↥(Submodule.span (Localization.AtPrime p) (H : Set V)) ⧸
          (Submodule.span (Localization.AtPrime p) (G : Set V)).comap
            (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype) := by
  have := isLocalizedModule p H G
  have : IsLocalizedModule p.primeCompl (locMap p H G ∘ₗ e.toLinearMap) := inferInstance
  exact ((IsLocalizedModule.iso p.primeCompl (locMap p H G ∘ₗ e.toLinearMap)).extendScalarsOfIsLocalization
    p.primeCompl (Localization.AtPrime p)).length_eq

end Formalism.L2.Pj.QAt.TieLDB
