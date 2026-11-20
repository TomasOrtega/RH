import Mathlib

namespace GlobalTheory

section CancelSummand

variable {R M M' P : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup P] [Module R P]

/- English proof (translation)
Use `set d : P →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ LinearMap.inr R M P with hd_def`. Set `dE : P ≃ₗ[R] P` to `LinearEquiv.ofBijective d hd`. Set `c : M →ₗ[R] P` to `(LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ LinearMap.inl R M P`. Set `φ : M →ₗ[R] M'` to `(LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ (LinearMap.prod LinearMap.id (-((dE.symm : P →ₗ[R] P) ∘ₗ c)))`. Set `ψ : M' →ₗ[R] M` to `(LinearMap.fst R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ LinearMap.inl R M' P`.

Establish `hsplit : ∀ x : M × P, (e x).2 = c x.1 + d x.2`. Introduce `x`. Establish `hx : x = ((x.1, 0) : M × P) + (0, x.2)` using `by simp`. Use `conv_lhs => rw [hx]`. Rewrite using `[map_add]`.

Both sides reduce to the same expression. Establish `hdd : ∀ p : P, d (dE.symm p) = p` using `fun p => dE.apply_symm_apply p`. Establish `key : ∀ m : M, e (m, -dE.symm (c m)) = (φ m, 0)`. Introduce `m`. Use `ext`.

Both sides reduce to the same expression. Rewrite using `[hsplit]`. Simplify using `only [map_neg, hdd]`. Simplify using the standard rewrite rules. Use `⟨LinearEquiv.ofLinear φ ψ ?_ ?_⟩` and prove the remaining obligations.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `m'`. Use `set x := e.symm (m', 0) with hx`. Establish `hex : e x = (m', 0)` using `by simp [hx]`. Establish `hp : -dE.symm (c x.1) = x.2`.

Establish `h0` using `hsplit x`. Rewrite `h0` using `[hex]`. Establish `h1 : d x.2 = -c x.1`. Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`. Conclude with `h0.symm`.

Establish `h2 : dE.symm (d x.2) = x.2` using `dE.symm_apply_apply x.2`. Rewrite `h2` using `[h1, map_neg]`. Conclude with `h2`. Establish `hk` using `key x.1`. Rewrite `hk` using `[hp]`.

Establish `hψ : ψ m' = x.1` using `rfl`. Use `show φ (ψ m') = m'`. Rewrite using `[hψ]`. Establish `h3 : ((φ x.1, (0 : P)) : M' × P) = (m', 0)` using `by rw [← hk]; exact hex`. Conclude with `congrArg Prod.fst h3`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `m`. Use `show ψ (φ m) = m`. Establish `h : ψ (φ m) = (e.symm (φ m, 0)).1` using `rfl`. Rewrite using `[h, ← key m, LinearEquiv.symm_apply_apply]`.
-/
theorem linearEquiv_of_prod_corner_bijective (e : (M × P) ≃ₗ[R] (M' × P))
    (hd : Function.Bijective ((LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P)) :
    Nonempty (M ≃ₗ[R] M') := by
  set d : P →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P with hd_def
  let dE : P ≃ₗ[R] P := LinearEquiv.ofBijective d hd
  let c : M →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inl R M P
  let φ : M →ₗ[R] M' := (LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      (LinearMap.prod LinearMap.id (-((dE.symm : P →ₗ[R] P) ∘ₗ c)))
  let ψ : M' →ₗ[R] M := (LinearMap.fst R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inl R M' P
  have hsplit : ∀ x : M × P, (e x).2 = c x.1 + d x.2 := by
    intro x
    have hx : x = ((x.1, 0) : M × P) + (0, x.2) := by simp
    conv_lhs => rw [hx]
    rw [map_add]
    rfl
  have hdd : ∀ p : P, d (dE.symm p) = p := fun p => dE.apply_symm_apply p
  have key : ∀ m : M, e (m, -dE.symm (c m)) = (φ m, 0) := by
    intro m
    ext
    · rfl
    · rw [hsplit]
      simp only [map_neg, hdd]
      simp
  refine ⟨LinearEquiv.ofLinear φ ψ ?_ ?_⟩
  · apply LinearMap.ext
    intro m'
    set x := e.symm (m', 0) with hx
    have hex : e x = (m', 0) := by simp [hx]
    have hp : -dE.symm (c x.1) = x.2 := by
      have h0 := hsplit x
      rw [hex] at h0
      have h1 : d x.2 = -c x.1 := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0.symm
      have h2 : dE.symm (d x.2) = x.2 := dE.symm_apply_apply x.2
      rw [h1, map_neg] at h2
      exact h2
    have hk := key x.1
    rw [hp] at hk
    have hψ : ψ m' = x.1 := rfl
    show φ (ψ m') = m'
    rw [hψ]
    have h3 : ((φ x.1, (0 : P)) : M' × P) = (m', 0) := by rw [← hk]; exact hex
    exact congrArg Prod.fst h3
  · apply LinearMap.ext
    intro m
    show ψ (φ m) = m
    have h : ψ (φ m) = (e.symm (φ m, 0)).1 := rfl
    rw [h, ← key m, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Use `set d : Module.End R P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ LinearMap.inr R M P with hd_def`. Distinguish the cases in `hd : Function.Bijective d`. Conclude with `linearEquiv_of_prod_corner_bijective e hd`. Set `b : P →ₗ[R] M'` to `(LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ LinearMap.inr R M P`. Set `c' : M' →ₗ[R] P` to `(LinearMap.snd R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ LinearMap.inl R M' P`.

Set `d' : Module.End R P` to `(LinearMap.snd R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ LinearMap.inr R M' P`. Establish `hsum : c' ∘ₗ b = 1 - d' * d`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `p`. Establish `h : e (0, p) = ((b p, 0) : M' × P) + (0, d p)`.

Use `ext`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Establish `h2` using `congrArg Prod.snd (e.symm_apply_apply (0, p))`. Rewrite `h2` using `[h, map_add]`. Use `show c' (b p) = p - d' (d p)`. Rewrite using `[eq_sub_iff_add_eq]`. Conclude with `h2`.

Establish `hnil : IsNilpotent (d' * d)`. Break down `hP (d' * d) with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Apply `hd` to reduce the goal to its premises.

Establish `hinj : Function.Injective d` using `fun x y hxy => h.1 (by show d' (d x) = d' (d y)`. Rewrite using `[hxy])`. Break down `hP d with ⟨n, hn⟩ | h2` into its components or cases. Establish `hsub : ∀ x : P, x = 0`. Introduce `x`.

Apply `hinj.iterate n` to reduce the goal to its premises. Establish `h3 : (d ^ n) x = (d ^ n) 0` using `by rw [hn]; simp`. Simplify `h3` using `[Module.End.pow_apply]`. Conclude with `⟨hinj, fun y => ⟨0, by rw [map_zero, hsub y]⟩⟩`. Conclude with `h2`.

Establish `hw : IsUnit (c' ∘ₗ b : Module.End R P)`. Rewrite using `[hsum]`. Conclude with `hnil.isUnit_one_sub`. Set `winv : Module.End R P` to `↑(hw.unit⁻¹)`. Set `g : M' →ₗ[R] P` to `((1 - d) * winv) ∘ₗ c'`.

Set `τ : (M' × P) ≃ₗ[R] (M' × P)` to `LinearEquiv.skewProd (LinearEquiv.refl R M') (LinearEquiv.refl R P) g`. Establish `hcorner : (LinearMap.snd R M' P) ∘ₗ ((e.trans τ : (M × P) ≃ₗ[R] (M' × P)) : (M × P) →ₗ[R] (M' × P)) ∘ₗ LinearMap.inr R M P = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `p`. Establish `h1 : g (b p) = p - d p`.

Establish `h4 : (winv * (c' ∘ₗ b : Module.End R P)) p = p`. Rewrite using `[hw.val_inv_mul]`. Both sides reduce to the same expression. Use `show ((1 - d) * winv) (c' (b p)) = p - d p`. Express the relevant statement in the definitionally equal form `(1 - d) ((winv * (c' ∘ₗ b : Module.End R P)) p) = p - d p`.

Rewrite using `[h4]`. Simplify using the standard rewrite rules. Use `show (e (0, p)).2 + g ((e (0, p)).1) = p`. Express the relevant statement in the definitionally equal form `d p + g (b p) = p`. Rewrite using `[h1]`.

Normalize the expressions using the abelian group laws. Conclude with `linearEquiv_of_prod_corner_bijective (e.trans τ) (by rw [hcorner]; exact Function.bijective_id)`.
-/
theorem linearEquiv_cancel_of_nilpotent_or_bijective
    (hP : ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f)
    (e : (M × P) ≃ₗ[R] (M' × P)) : Nonempty (M ≃ₗ[R] M') := by
  set d : Module.End R P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P with hd_def
  by_cases hd : Function.Bijective d
  · exact linearEquiv_of_prod_corner_bijective e hd
  let b : P →ₗ[R] M' := (LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P
  let c' : M' →ₗ[R] P := (LinearMap.snd R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inl R M' P
  let d' : Module.End R P := (LinearMap.snd R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inr R M' P
  have hsum : c' ∘ₗ b = 1 - d' * d := by
    apply LinearMap.ext
    intro p
    have h : e (0, p) = ((b p, 0) : M' × P) + (0, d p) := by
      ext
      · simp; rfl
      · simp; rfl
    have h2 := congrArg Prod.snd (e.symm_apply_apply (0, p))
    rw [h, map_add] at h2
    show c' (b p) = p - d' (d p)
    rw [eq_sub_iff_add_eq]
    exact h2
  have hnil : IsNilpotent (d' * d) := by
    rcases hP (d' * d) with h | h
    · exact h
    · exfalso
      apply hd
      have hinj : Function.Injective d := fun x y hxy => h.1 (by
        show d' (d x) = d' (d y)
        rw [hxy])
      rcases hP d with ⟨n, hn⟩ | h2
      · have hsub : ∀ x : P, x = 0 := by
          intro x
          apply hinj.iterate n
          have h3 : (d ^ n) x = (d ^ n) 0 := by rw [hn]; simp
          simpa [Module.End.pow_apply] using h3
        exact ⟨hinj, fun y => ⟨0, by rw [map_zero, hsub y]⟩⟩
      · exact h2
  have hw : IsUnit (c' ∘ₗ b : Module.End R P) := by
    rw [hsum]; exact hnil.isUnit_one_sub
  let winv : Module.End R P := ↑(hw.unit⁻¹)
  let g : M' →ₗ[R] P := ((1 - d) * winv) ∘ₗ c'
  let τ : (M' × P) ≃ₗ[R] (M' × P) :=
    LinearEquiv.skewProd (LinearEquiv.refl R M') (LinearEquiv.refl R P) g
  have hcorner : (LinearMap.snd R M' P) ∘ₗ ((e.trans τ : (M × P) ≃ₗ[R] (M' × P)) :
      (M × P) →ₗ[R] (M' × P)) ∘ₗ LinearMap.inr R M P = LinearMap.id := by
    apply LinearMap.ext
    intro p
    have h1 : g (b p) = p - d p := by
      have h4 : (winv * (c' ∘ₗ b : Module.End R P)) p = p := by
        rw [hw.val_inv_mul]; rfl
      show ((1 - d) * winv) (c' (b p)) = p - d p
      change (1 - d) ((winv * (c' ∘ₗ b : Module.End R P)) p) = p - d p
      rw [h4]
      simp
    show (e (0, p)).2 + g ((e (0, p)).1) = p
    change d p + g (b p) = p
    rw [h1]
    abel
  exact linearEquiv_of_prod_corner_bijective (e.trans τ) (by rw [hcorner]; exact Function.bijective_id)

end CancelSummand

/- English proof (translation)
Introduce `R M M' P _ _ _ _ _ _ _ hP he`. Take `⟨e⟩` from `he`. Conclude with `linearEquiv_cancel_of_nilpotent_or_bijective hP e`.
-/
theorem cancel_summand_nilpotent_or_bijective : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P],
    (∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f) →
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  intro R M M' P _ _ _ _ _ _ _ hP he
  obtain ⟨e⟩ := he
  exact linearEquiv_cancel_of_nilpotent_or_bijective hP e

end GlobalTheory
