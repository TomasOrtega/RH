import Mathlib

open AlgebraicGeometry

/- English proof (translation)
Take `⟨t, rfl⟩` from `(IsNoetherian.noetherian I : I.FG)`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => exact ⟨1, M.one_mem, by simp⟩`. Consider the case `insert x t _ ih`. Take `⟨s, hs, hs'⟩` from `ih fun a ha => h a (Ideal.span_mono (by simp) ha)`.

Take `⟨m, hm, hm'⟩` from `h x (Ideal.subset_span (by simp))`. Use `⟨m * s, M.mul_mem hm hs, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite `ha` using `[Finset.coe_insert, Submodule.mem_span_insert]`. Take `⟨c, z, hz, rfl⟩` from `ha`. Establish `h2` using `hs' z hz`.

Rewrite using `[smul_eq_mul]`. Take the linear combination `(s * c) * hm' + m * h2`.
-/
private lemma exists_kill {A : Type*} [CommRing A] [IsNoetherianRing A] (M : Submonoid A)
    (I : Ideal A) (h : ∀ a ∈ I, ∃ m ∈ M, m * a = 0) :
    ∃ s ∈ M, ∀ a ∈ I, s * a = 0 := by
  classical
  obtain ⟨t, rfl⟩ := (IsNoetherian.noetherian I : I.FG)
  induction t using Finset.induction_on with
  | empty => exact ⟨1, M.one_mem, by simp⟩
  | insert x t _ ih =>
    obtain ⟨s, hs, hs'⟩ := ih fun a ha => h a (Ideal.span_mono (by simp) ha)
    obtain ⟨m, hm, hm'⟩ := h x (Ideal.subset_span (by simp))
    refine ⟨m * s, M.mul_mem hm hs, fun a ha => ?_⟩
    rw [Finset.coe_insert, Submodule.mem_span_insert] at ha
    obtain ⟨c, z, hz, rfl⟩ := ha
    have h2 := hs' z hz
    rw [smul_eq_mul]
    linear_combination (s * c) * hm' + m * h2

/- English proof (translation)
Establish `hu : IsUnit (algebraMap A L s)` using `IsLocalization.map_units L (⟨s, hs⟩ : M)`. Set `φ : B →+* L` to `IsLocalization.Away.lift s hu`. Establish `hφ : ∀ a, φ (algebraMap A B a) = algebraMap A L a` using `fun a => IsLocalization.Away.lift_eq s hu a`. Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `b hb`. Take `⟨⟨a, m⟩, hm⟩` from `IsLocalization.surj (Submonoid.powers s) b`. Establish `h0 : algebraMap A L a = 0`. Rewrite using `[← hφ, ← hm, map_mul, hb, zero_mul]`. Establish `h1 : algebraMap A B s * algebraMap A B a = 0`.

Rewrite using `[← map_mul, hk a h0, map_zero]`. Establish `hsu : IsUnit (algebraMap A B s)` using `IsLocalization.Away.algebraMap_isUnit s`. Establish `h2 : algebraMap A B a = 0` using `(hsu.mul_right_eq_zero).mp h1`. Establish `hmu : IsUnit (algebraMap A B (m : A))` using `IsLocalization.map_units B m`. Simplify using `only at hm`.

Rewrite `hm` using `[h2]`. Conclude with `(hmu.mul_left_eq_zero).mp hm`. Conclude with `hinj.isDomain φ`.
-/
private lemma isDomain_away {A L B : Type*} [CommRing A] [CommRing L] [IsDomain L]
    [CommRing B] [Algebra A L] [Algebra A B] (M : Submonoid A) [IsLocalization M L]
    (s : A) (hs : s ∈ M) (hk : ∀ a, algebraMap A L a = 0 → s * a = 0)
    [IsLocalization.Away s B] : IsDomain B := by
  have hu : IsUnit (algebraMap A L s) := IsLocalization.map_units L (⟨s, hs⟩ : M)
  let φ : B →+* L := IsLocalization.Away.lift s hu
  have hφ : ∀ a, φ (algebraMap A B a) = algebraMap A L a := fun a =>
    IsLocalization.Away.lift_eq s hu a
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) b
    have h0 : algebraMap A L a = 0 := by
      rw [← hφ, ← hm, map_mul, hb, zero_mul]
    have h1 : algebraMap A B s * algebraMap A B a = 0 := by
      rw [← map_mul, hk a h0, map_zero]
    have hsu : IsUnit (algebraMap A B s) := IsLocalization.Away.algebraMap_isUnit s
    have h2 : algebraMap A B a = 0 := (hsu.mul_right_eq_zero).mp h1
    have hmu : IsUnit (algebraMap A B (m : A)) :=
      IsLocalization.map_units B m
    simp only at hm
    rw [h2] at hm
    exact (hmu.mul_left_eq_zero).mp hm
  exact hinj.isDomain φ

/- English proof (translation)
Introduce `X V hV _ ξ hξ _`. Use `letI alg : Algebra Γ(X, V) (X.presheaf.stalk ξ) := X.presheaf.algebra_section_stalk (⟨ξ, hξ⟩ : V)`. Set `P` to `(hV.primeIdealOf ⟨ξ, hξ⟩).asIdeal`. Establish `hloc : IsLocalization P.primeCompl (X.presheaf.stalk ξ)` using `hV.isLocalization_stalk ⟨ξ, hξ⟩`. Take `⟨s, hs, hk⟩` from `exists_kill P.primeCompl (RingHom.ker (algebraMap Γ(X, V) (X.presheaf.stalk ξ))) (fun a ha => by`.

Take `⟨m, hm⟩` from `(IsLocalization.map_eq_zero_iff P.primeCompl (X.presheaf.stalk ξ) a).mp ha`. Conclude with `⟨m, m.2, hm⟩)`. Use `⟨s, ?_, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk ξ) s)` using `IsLocalization.map_units (X.presheaf.stalk ξ) (⟨s, hs⟩ : P.primeCompl)`. Conclude with `(X.mem_basicOpen s ξ hξ).mpr hu`.

Use `hV.isLocalization_basicOpen s` as an intermediate fact. Conclude with `isDomain_away (L := X.presheaf.stalk ξ) P.primeCompl s hs (fun a ha => hk a ha)`.
-/
theorem UpperTheory.Reformulated.B.DYde8.main :
    ∀ {X : AlgebraicGeometry.Scheme} {V : X.Opens},
      AlgebraicGeometry.IsAffineOpen V →
        ∀ [IsNoetherianRing (↑(X.presheaf.obj (Opposite.op V)) : Type)],
          ∀ ξ ∈ V,
            ∀ [IsDomain (↑(X.presheaf.stalk ξ) : Type)],
              ∃ (f : (↑(X.presheaf.obj (Opposite.op V)) : Type)),
                ξ ∈ X.basicOpen f ∧ IsDomain (↑(X.presheaf.obj (Opposite.op (X.basicOpen f))) : Type) := by
  intro X V hV _ ξ hξ _
  letI alg : Algebra Γ(X, V) (X.presheaf.stalk ξ) :=
    X.presheaf.algebra_section_stalk (⟨ξ, hξ⟩ : V)
  let P := (hV.primeIdealOf ⟨ξ, hξ⟩).asIdeal
  have hloc : IsLocalization P.primeCompl (X.presheaf.stalk ξ) :=
    hV.isLocalization_stalk ⟨ξ, hξ⟩
  obtain ⟨s, hs, hk⟩ := exists_kill P.primeCompl
    (RingHom.ker (algebraMap Γ(X, V) (X.presheaf.stalk ξ)))
    (fun a ha => by
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl (X.presheaf.stalk ξ) a).mp ha
      exact ⟨m, m.2, hm⟩)
  refine ⟨s, ?_, ?_⟩
  · have hu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk ξ) s) :=
      IsLocalization.map_units (X.presheaf.stalk ξ) (⟨s, hs⟩ : P.primeCompl)
    exact (X.mem_basicOpen s ξ hξ).mpr hu
  · have := hV.isLocalization_basicOpen s
    exact isDomain_away (L := X.presheaf.stalk ξ) P.primeCompl s hs (fun a ha => hk a ha)
