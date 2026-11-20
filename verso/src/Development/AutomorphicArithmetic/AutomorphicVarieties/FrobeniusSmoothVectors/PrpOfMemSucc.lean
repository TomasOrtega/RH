import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Use extensionality with `a b`. Use `show (if pw a b = j then X a b else 0) = X a b`. Use `split_ifs with h`. Both sides reduce to the same expression. Conclude with `(hX a b h).symm`.
-/
private theorem prp_of_mem {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (hX : X ∈ adp K j) : ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) = X := by
  ext a b
  show (if pw a b = j then X a b else 0) = X a b
  split_ifs with h
  · rfl
  · exact (hX a b h).symm

/- English proof (translation)
Use extensionality with `a b`. Use `show (if pw a b = j then X a b else 0) = 0`. Use `split_ifs with h`. Establish `hne : ∀ p q : ZMod 2, p = q → p ≠ q + 1` using `by decide`. Conclude with `hX a b (hne _ _ h)`.

Both sides reduce to the same expression.
-/
private theorem prp_of_mem_succ {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (hX : X ∈ adp K (j + 1)) : ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext a b
  show (if pw a b = j then X a b else 0) = 0
  split_ifs with h
  · have hne : ∀ p q : ZMod 2, p = q → p ≠ q + 1 := by decide
    exact hX a b (hne _ _ h)
  · rfl

/- English proof (translation)
Use extensionality with `a b`. Use `show X a b = (if pw a b = j then X a b else 0) + (if pw a b = j + 1 then X a b else 0)`. Establish `hc : ∀ p q : ZMod 2, (p = q ∧ p ≠ q + 1) ∨ (p ≠ q ∧ p = q + 1)` using `by decide`. Break down `hc (pw a b) j with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Rewrite using `[if_pos h1, if_neg h2, add_zero]`.

Rewrite using `[if_neg h1, if_pos h2, zero_add]`.
-/
private theorem prp_add {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K) :
    X = ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) + (prp K (j + 1) X : adp K (j + 1)) := by
  ext a b
  show X a b = (if pw a b = j then X a b else 0) + (if pw a b = j + 1 then X a b else 0)
  have hc : ∀ p q : ZMod 2, (p = q ∧ p ≠ q + 1) ∨ (p ≠ q ∧ p = q + 1) := by decide
  rcases hc (pw a b) j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2, add_zero]
  · rw [if_neg h1, if_pos h2, zero_add]

/- English proof (translation)
Introduce `l _ k _ F K _ h2 B π h`. Establish `P1 : ∀ j s X, prp K j (B.ad s X) = h.ad j s (prp K j X)`. Introduce `j s X`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Box.Ev.ad_apply]`.

Use `conv_lhs => rw [prp_add j X]`. Rewrite using `[map_add, map_add, Submodule.coe_add, prp_of_mem j _ (h.stab j s (prp K j X).2), prp_of_mem_succ j _ (h.stab (j + 1) s (prp K (j + 1) X).2), add_zero]`. Use `⟨P1, ?_⟩` and prove the remaining obligations. Introduce `j χ hχ f hf`. Establish `hF` using `hχ (f.comp (prp K j)) (fun g X => by simp only [LinearMap.comp_apply, P1, hf])`.

Use extensionality with `v`. Use `LinearMap.congr_fun hF (v : Matrix (Fin 3) (Fin 3) K)` as an intermediate fact. Establish `hv : prp K j (v : Matrix (Fin 3) (Fin 3) K) = v` using `Subtype.ext (prp_of_mem j _ v.2)`. Simplify `this` using `[hv]`.
-/
theorem UpperTheory.V.Fr.ep_prp :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), (∀ j s X, prp K j (B.ad s X) = h.ad j s (prp K j X)) ∧ ∀ (j : ZMod 2) (χ : F.Γ → K), (∀ f : Matrix (Fin 3) (Fin 3) K →ₗ[K] K, (∀ g X, f (B.ad g X) = χ g * f X) → f = 0) → ∀ f : adp K j →ₗ[K] K, (∀ g X, f (h.ad j g X) = χ g * f X) → f = 0 := by
  intro l _ k _ F K _ h2 B π h
  have P1 : ∀ j s X, prp K j (B.ad s X) = h.ad j s (prp K j X) := by
    intro j s X
    apply Subtype.ext
    rw [Box.Ev.ad_apply]
    conv_lhs => rw [prp_add j X]
    rw [map_add, map_add, Submodule.coe_add,
      prp_of_mem j _ (h.stab j s (prp K j X).2),
      prp_of_mem_succ j _ (h.stab (j + 1) s (prp K (j + 1) X).2), add_zero]
  refine ⟨P1, ?_⟩
  intro j χ hχ f hf
  have hF := hχ (f.comp (prp K j)) (fun g X => by simp only [LinearMap.comp_apply, P1, hf])
  ext v
  have := LinearMap.congr_fun hF (v : Matrix (Fin 3) (Fin 3) K)
  have hv : prp K j (v : Matrix (Fin 3) (Fin 3) K) = v := Subtype.ext (prp_of_mem j _ v.2)
  simpa [hv] using this
