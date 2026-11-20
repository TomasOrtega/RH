import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `Z S A D _ _ _ _ _ z a N q x hN hli ⟨d, w, hw⟩`. Use `letI : Module Z N := Module.compHom _ (a.comp z)`. Establish `hsm : ∀ (r : Z) (n : N), ((r • n : N) : D) = a (z r) • (n : D)` using `fun _ _ => rfl`. Set `f : (Fin q → Fin d → Z) →ₗ[Z] N` to `{ toFun := fun c => ⟨∑ i, a (∑ m, z (c i m) * w m) • x i, (hN _).2 ⟨_, rfl⟩⟩ map_add' := fun c c' => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[add_mul, Finset.sum_add_distrib, add_smul]`. Use the proof step `map_smul' := fun r c => by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hsm]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum, smul_smul, mul_assoc, ← Finset.mul_sum] }`.

Establish `hinj : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Establish `h1` using `hli (fun i => ∑ m, z (c i m) * w m) (congrArg Subtype.val hc)`. Use function extensionality and compare the values at `i`.

Establish `h2 : (0 : S) = ∑ m, z (c i m) * w m` using `(congrFun h1 i).symm`. Conclude with `(hw 0).unique h2 (by simp)`. Establish `hsurj : Function.Surjective f`. Introduce and unpack `⟨y, hy⟩`. Take `⟨s, rfl⟩` from `(hN y).1 hy`.

Use `choose c hc _ using fun i => hw (s i)`. Use `⟨c, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∑ i, a (∑ m, z (c i m) * w m) • x i = ∑ i, a (s i) • x i`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [← hc i]`. Conclude with `Module.Projective.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)`.
-/
theorem projective_compHom_of_free_of_finite_free :
    ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by
  intro Z S A D _ _ _ _ _ z a N q x hN hli ⟨d, w, hw⟩
  letI : Module Z N := Module.compHom _ (a.comp z)
  have hsm : ∀ (r : Z) (n : N), ((r • n : N) : D) = a (z r) • (n : D) := fun _ _ => rfl
  let f : (Fin q → Fin d → Z) →ₗ[Z] N :=
    { toFun := fun c => ⟨∑ i, a (∑ m, z (c i m) * w m) • x i, (hN _).2 ⟨_, rfl⟩⟩
      map_add' := fun c c' => by
        apply Subtype.ext
        simp [add_mul, Finset.sum_add_distrib, add_smul]
      map_smul' := fun r c => by
        apply Subtype.ext
        rw [hsm]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum,
          smul_smul, mul_assoc, ← Finset.mul_sum] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 := hli (fun i => ∑ m, z (c i m) * w m) (congrArg Subtype.val hc)
    funext i
    have h2 : (0 : S) = ∑ m, z (c i m) * w m := (congrFun h1 i).symm
    exact (hw 0).unique h2 (by simp)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := (hN y).1 hy
    choose c hc _ using fun i => hw (s i)
    refine ⟨c, Subtype.ext ?_⟩
    change ∑ i, a (∑ m, z (c i m) * w m) • x i = ∑ i, a (s i) • x i
    exact Finset.sum_congr rfl fun i _ => by rw [← hc i]
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

end GlobalTheory
