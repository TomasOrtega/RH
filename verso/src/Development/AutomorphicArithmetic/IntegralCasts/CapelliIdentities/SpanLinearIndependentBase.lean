import Mathlib

/- English proof (translation)
Introduce `A Ω C E V I _ _ _ _ _ _ _ _ n φ ψ κ κ' F hφ hF hspan`. Establish `hlat : ∀ e ∈ Submodule.span (↥φ.range) {e : E | ∃ a : Fin n → A, κ e = fun i => φ (a i)}, ∃ a : Fin n → A, κ e = fun i => φ (a i)`. Introduce `e he`. Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`.

Consider the case `zero => exact ⟨0, by ext i; simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by ext i; simp [ha, hb]⟩`.

Consider the case `smul c x _ hx`. Take `⟨a, ha⟩` from `hx`. Take `⟨c, r, rfl⟩` from `c`. Use `⟨r • a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `κ (φ r • x) = _`.

Use extensionality with `i`. Simplify using `[ha]`. Establish `ha : ∀ j, ∃ a : Fin n → A, κ (F j) = fun i => φ (a i)` using `fun j => hlat _ (hspan ▸ Submodule.subset_span ⟨j, rfl⟩)`. Use `choose a ha using ha`. Establish `hb : ∀ k : Fin n, ∃ b : I → A, ∀ i, ∑ j, a j i * b j = (1 : Matrix (Fin n) (Fin n) A) i k`.

Introduce `k`. Establish `hk : κ.symm (fun i => φ ((1 : Matrix (Fin n) (Fin n) A) i k)) ∈ Submodule.span (↥φ.range) (Set.range F)`. Rewrite using `[← hspan]`. Conclude with `Submodule.subset_span ⟨fun i => (1 : Matrix (Fin n) (Fin n) A) i k, by simp⟩`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hk`.

Use `choose b hb using fun j => (c j).2`. Use `⟨b, fun i => hφ ?_⟩` and prove the remaining obligations. Establish `h1 : ∑ j, φ (b j) • F j = κ.symm (fun i => φ ((1 : Matrix (Fin n) (Fin n) A) i k))`. Rewrite using `[← hc]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hb j]; rfl`.

Establish `h2` using `congrFun (congrArg κ h1) i`. Rewrite `h2` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[← h2]`. Simplify using `[ha, mul_comm]`. Use `choose b hb using hb`.

Use `set P : Matrix (Fin n) I A := Matrix.of fun i j => a j i with hP`. Use `set Q : Matrix I (Fin n) A := Matrix.of fun j k => b k j with hQ`. Establish `hPQ : P * Q = 1`. Use extensionality with `i k`. Simplify `hb k i` using `[Matrix.mul_apply, hP, hQ]`.

Establish `hQP : Q * P = 1`. Establish `hD : P * (Q * P - 1) = 0`. Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_one, sub_self]`. Rewrite using `[← sub_eq_zero]`. Generalize the expression as in `Q * P - 1 = D at hD`.

Use extensionality with `l j`. Establish `h0 : ∑ l, φ (D l j) • F l = 0`. Apply `κ.injective` to reduce the goal to its premises. Use extensionality with `i`. Establish `h3` using `congrArg φ (congrFun (congrFun hD i) j)`.

Simplify `h3` using `[Matrix.mul_apply, hP, ha, mul_comm]`. Apply `hφ` to reduce the goal to its premises. Simplify using `using Fintype.linearIndependent_iff.1 hF _ h0 l`. Establish `h1 : Q.map ψ * P.map ψ = 1`. Rewrite using `[← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero ψ) (map_one ψ)]`.

Establish `h2 : P.map ψ * Q.map ψ = 1`. Rewrite using `[← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero ψ) (map_one ψ)]`. Use `⟨(Pi.basisFun C I).map ((Matrix.toLin'OfInv h1 h2).trans κ'.symm), fun j => ⟨a j, ha j, ?_⟩⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[Matrix.toLin'OfInv, hP]`.
-/
theorem UpperTheory.span_linear_independent_base :
    ∀ {A Ω C E V I : Type} [CommRing A] [Field Ω] [Field C] [AddCommGroup E] [Module Ω E] [AddCommGroup V]
          [Module C V] [Fintype I] {n : ℕ} (φ : A →+* Ω) (ψ : A →+* C) (κ : E ≃ₗ[Ω] (Fin n → Ω)) (κ' : V ≃ₗ[C] (Fin n → C))
          (F : I → E), Function.Injective φ → LinearIndependent Ω F →
          Submodule.span (↥φ.range) {e : E | ∃ a : Fin n → A, κ e = fun i => φ (a i)} =
            Submodule.span (↥φ.range) (Set.range F) →
          ∃ y : Module.Basis I C V, ∀ j, ∃ a : Fin n → A, (κ (F j) = fun i => φ (a i)) ∧ κ' (y j) = fun i => ψ (a i) := by
  intro A Ω C E V I _ _ _ _ _ _ _ _ n φ ψ κ κ' F hφ hF hspan
  classical
  have hlat : ∀ e ∈ Submodule.span (↥φ.range) {e : E | ∃ a : Fin n → A, κ e = fun i => φ (a i)},
      ∃ a : Fin n → A, κ e = fun i => φ (a i) := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, by ext i; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by ext i; simp [ha, hb]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, r, rfl⟩ := c
      refine ⟨r • a, ?_⟩
      change κ (φ r • x) = _
      ext i
      simp [ha]
  have ha : ∀ j, ∃ a : Fin n → A, κ (F j) = fun i => φ (a i) := fun j =>
    hlat _ (hspan ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose a ha using ha
  have hb : ∀ k : Fin n, ∃ b : I → A, ∀ i, ∑ j, a j i * b j = (1 : Matrix (Fin n) (Fin n) A) i k := by
    intro k
    have hk : κ.symm (fun i => φ ((1 : Matrix (Fin n) (Fin n) A) i k)) ∈
        Submodule.span (↥φ.range) (Set.range F) := by
      rw [← hspan]
      exact Submodule.subset_span ⟨fun i => (1 : Matrix (Fin n) (Fin n) A) i k, by simp⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hk
    choose b hb using fun j => (c j).2
    refine ⟨b, fun i => hφ ?_⟩
    have h1 : ∑ j, φ (b j) • F j = κ.symm (fun i => φ ((1 : Matrix (Fin n) (Fin n) A) i k)) := by
      rw [← hc]
      exact Finset.sum_congr rfl fun j _ => by rw [hb j]; rfl
    have h2 := congrFun (congrArg κ h1) i
    rw [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    simp [ha, mul_comm]
  choose b hb using hb
  set P : Matrix (Fin n) I A := Matrix.of fun i j => a j i with hP
  set Q : Matrix I (Fin n) A := Matrix.of fun j k => b k j with hQ
  have hPQ : P * Q = 1 := by
    ext i k
    simpa [Matrix.mul_apply, hP, hQ] using hb k i
  have hQP : Q * P = 1 := by
    have hD : P * (Q * P - 1) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_one, sub_self]
    rw [← sub_eq_zero]
    generalize Q * P - 1 = D at hD
    ext l j
    have h0 : ∑ l, φ (D l j) • F l = 0 := by
      apply κ.injective
      ext i
      have h3 := congrArg φ (congrFun (congrFun hD i) j)
      simpa [Matrix.mul_apply, hP, ha, mul_comm] using h3
    apply hφ
    simpa using Fintype.linearIndependent_iff.1 hF _ h0 l
  have h1 : Q.map ψ * P.map ψ = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have h2 : P.map ψ * Q.map ψ = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  refine ⟨(Pi.basisFun C I).map ((Matrix.toLin'OfInv h1 h2).trans κ'.symm), fun j => ⟨a j, ha j, ?_⟩⟩
  ext i
  simp [Matrix.toLin'OfInv, hP]
