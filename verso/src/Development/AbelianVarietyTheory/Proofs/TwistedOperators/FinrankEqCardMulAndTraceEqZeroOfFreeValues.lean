import Mathlib

namespace GlobalTheory

/- English proof (translation)
Set `b` to `Pi.basis (fun _ : X => Module.finBasis ℂ W)`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_repr, Pi.basis_apply, hM, Pi.single_eq_of_ne (hπ i.1), map_zero, map_zero, Finsupp.zero_apply]`.
-/
theorem trace_eq_zero_of_coord_move {X W : Type} [Fintype X] [DecidableEq X] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (π : X → X) (hπ : ∀ c, π c ≠ c)
    (φ : X → Module.End ℂ W) (M : Module.End ℂ (X → W)) (hM : ∀ f c, M f c = φ c (f (π c))) :
    LinearMap.trace ℂ (X → W) M = 0 := by
  classical

  let b := Pi.basis (fun _ : X => Module.finBasis ℂ W)
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_repr, Pi.basis_apply, hM,
    Pi.single_eq_of_ne (hπ i.1), map_zero, map_zero, Finsupp.zero_apply]

/- English proof (translation)
Introduce `Y X B W _ _ _ _ _ _ cls ev S hcls hinj hcls_eq hfree`. Use `haveI : Fintype X := Fintype.ofFinite X`. Take `⟨s, hs⟩ : ∃ s : X → Y, ∀ x, cls (s x) = x` from `⟨fun x => (hcls x).choose, fun x => (hcls x).choose_spec⟩`. Set `Φ : S →ₗ[ℂ] (X → W)` to `LinearMap.pi (fun x => (ev (s x)).comp S.subtype)`. Establish `hΦ : ∀ (T : S) x, Φ T x = ev (s x) T` using `fun _ _ => rfl`.

Establish `hzero : ∀ T ∈ S, (∀ x, ev (s x) T = 0) → T = 0`. Introduce `T hT h0`. Apply `hinj` to reduce the goal to its premises. Introduce `h`. Take `⟨φ, hφ⟩` from `hcls_eq (s (cls h)) h (hs _)`.

Rewrite using `[hφ T hT, h0, map_zero]`. Establish `hΦinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `T hT`. Use `Subtype.ext (hzero T T.2 (fun x => ?_))` and prove the remaining obligations.

Establish `hx` using `congrFun hT x`. Rewrite `hx` using `[hΦ]`. Conclude with `hx`. Establish `hΦsurj : Function.Surjective Φ`. Introduce `g`.

Use `choose T hTS hTg hT0 using fun x => hfree (s x) (g x)`. Use `⟨⟨∑ x, T x, Submodule.sum_mem _ (fun x _ => hTS x)⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Use `show ev (s y) (∑ x, T x) = g y`. Rewrite using `[map_sum, Finset.sum_eq_single y]`.

Conclude with `hTg y`. Introduce `x _ hxy`. Apply `hT0` to reduce the goal to its premises. Rewrite using `[hs, hs]`. Conclude with `Ne.symm hxy`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ y) h`. Set `Ψ : S ≃ₗ[ℂ] (X → W)` to `LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩`. Establish `hfd : FiniteDimensional ℂ S` using `LinearEquiv.finiteDimensional Ψ.symm`. Use `⟨hfd, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ψ.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]`. Introduce `H _ _ e he hrange A t hA ht`. Set `eS : H ≃ₗ[ℂ] S` to `(LinearEquiv.ofInjective e he).trans (LinearEquiv.ofEq _ _ hrange)`. Set `Θ : H ≃ₗ[ℂ] (X → W)` to `eS.trans Ψ`. Establish `hΘ : ∀ x c, Θ x c = ev (s c) (e x)` using `fun _ _ => rfl`.

Use `haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional Θ.symm`. Rewrite using `[← LinearMap.trace_conj' A Θ]`. Use `choose φ hφ using fun c => hcls_eq (s (cls (t (s c)))) (t (s c)) (hs _)`. Use `trace_eq_zero_of_coord_move (fun c => cls (t (s c))) (fun c => by have h := ht (s c); rwa [hs] at h) φ _ ?_` and prove the remaining obligations. Introduce `g c`.

Take `⟨x, rfl⟩` from `Θ.surjective g`. Rewrite using `[LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hΘ, hΘ, hA]`. Establish `hmem : e x ∈ S`. Rewrite using `[← hrange]`. Conclude with `LinearMap.mem_range_self e x`.

Conclude with `hφ c (e x) hmem`.
-/
theorem finrank_eq_card_mul_and_trace_eq_zero_of_free_values :
    ∀ (Y X B W : Type) [Finite X] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (cls : Y → X) (ev : Y → (B →ₗ[ℂ] W)) (S : Submodule ℂ B), Function.Surjective cls → (∀ T : B, (∀ h, ev h T = 0) → T = 0) → (∀ h h', cls h = cls h' → ∃ φ : Module.End ℂ W, ∀ T ∈ S, ev h' T = φ (ev h T)) → (∀ h (ℓ : W), ∃ T ∈ S, ev h T = ℓ ∧ ∀ h', cls h' ≠ cls h → ev h' T = 0) → FiniteDimensional ℂ S ∧ Module.finrank ℂ S = Nat.card X * Module.finrank ℂ W ∧ ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] B), Function.Injective e → LinearMap.range e = S → ∀ (A : Module.End ℂ H) (t : Y → Y), (∀ x h, ev h (e (A x)) = ev (t h) (e x)) → (∀ h, cls (t h) ≠ cls h) → LinearMap.trace ℂ H A = 0 := by
  intro Y X B W _ _ _ _ _ _ cls ev S hcls hinj hcls_eq hfree
  classical
  haveI : Fintype X := Fintype.ofFinite X

  obtain ⟨s, hs⟩ : ∃ s : X → Y, ∀ x, cls (s x) = x :=
    ⟨fun x => (hcls x).choose, fun x => (hcls x).choose_spec⟩

  let Φ : S →ₗ[ℂ] (X → W) := LinearMap.pi (fun x => (ev (s x)).comp S.subtype)
  have hΦ : ∀ (T : S) x, Φ T x = ev (s x) T := fun _ _ => rfl
  have hzero : ∀ T ∈ S, (∀ x, ev (s x) T = 0) → T = 0 := by
    intro T hT h0
    apply hinj
    intro h
    obtain ⟨φ, hφ⟩ := hcls_eq (s (cls h)) h (hs _)
    rw [hφ T hT, h0, map_zero]
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    refine Subtype.ext (hzero T T.2 (fun x => ?_))
    have hx := congrFun hT x
    rw [hΦ] at hx
    exact hx
  have hΦsurj : Function.Surjective Φ := by
    intro g
    choose T hTS hTg hT0 using fun x => hfree (s x) (g x)
    refine ⟨⟨∑ x, T x, Submodule.sum_mem _ (fun x _ => hTS x)⟩, ?_⟩
    funext y
    show ev (s y) (∑ x, T x) = g y
    rw [map_sum, Finset.sum_eq_single y]
    · exact hTg y
    · intro x _ hxy
      apply hT0
      rw [hs, hs]
      exact Ne.symm hxy
    · intro h
      exact absurd (Finset.mem_univ y) h
  let Ψ : S ≃ₗ[ℂ] (X → W) := LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hfd : FiniteDimensional ℂ S := LinearEquiv.finiteDimensional Ψ.symm
  refine ⟨hfd, ?_, ?_⟩
  · rw [Ψ.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
  · intro H _ _ e he hrange A t hA ht

    let eS : H ≃ₗ[ℂ] S := (LinearEquiv.ofInjective e he).trans (LinearEquiv.ofEq _ _ hrange)
    let Θ : H ≃ₗ[ℂ] (X → W) := eS.trans Ψ
    have hΘ : ∀ x c, Θ x c = ev (s c) (e x) := fun _ _ => rfl
    haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional Θ.symm
    rw [← LinearMap.trace_conj' A Θ]
    choose φ hφ using fun c => hcls_eq (s (cls (t (s c)))) (t (s c)) (hs _)
    refine trace_eq_zero_of_coord_move (fun c => cls (t (s c)))
      (fun c => by have h := ht (s c); rwa [hs] at h) φ _ ?_
    intro g c
    obtain ⟨x, rfl⟩ := Θ.surjective g
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hΘ, hΘ, hA]
    have hmem : e x ∈ S := by
      rw [← hrange]
      exact LinearMap.mem_range_self e x
    exact hφ c (e x) hmem

end GlobalTheory
