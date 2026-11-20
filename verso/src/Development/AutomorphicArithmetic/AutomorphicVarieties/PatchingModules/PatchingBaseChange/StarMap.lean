import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Introduce `l _ F O O' _ _ _ _ R R' _ _ _ _ g hg`. Establish `h1 : pushCh g (F.eps O R) = F.eps O' R'`. Use extensionality with `x`. Simplify using `[GFrame.eps, pushCh, hg]`. Establish `hs : ∀ (S : Type) [CommRing S] [Algebra O S] (n : ℕ) (h : F.G₀) (r : S), F.star O S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O S h ^ (1 - (n : ℤ)) : Sˣ) : S))`.

Introduce `S _ _ n h r`. Simplify using `[GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]`. Establish `hs' : ∀ (S : Type) [CommRing S] [Algebra O' S] (n : ℕ) (h : F.G₀) (r : S), F.star O' S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O' S h ^ (1 - (n : ℤ)) : Sˣ) : S))`. Introduce `S _ _ n h r`. Simplify using `[GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]`.

Establish `hadd : ∀ (n : ℕ) (a b : MonoidAlgebra R F.G₀), F.star O R n (a + b) = F.star O R n a + F.star O R n b`. Introduce `n a b`. Simplify using `[GFrame.star]`. Establish `hadd' : ∀ (n : ℕ) (a b : MonoidAlgebra R' F.G₀), F.star O' R' n (a + b) = F.star O' R' n a + F.star O' R' n b`. Introduce `n a b`.

Simplify using `[GFrame.star]`. Establish `hz : ∀ (n : ℕ), F.star O R n 0 = 0`. Introduce `n`. Simplify using `[GFrame.star]`. Establish `hz' : ∀ (n : ℕ), F.star O' R' n 0 = 0`.

Introduce `n`. Simplify using `[GFrame.star]`. Establish `he : ∀ (h : F.G₀) (k : ℤ), g ((F.eps O R h ^ k : Rˣ) : R) = ((F.eps O' R' h ^ k : R'ˣ) : R')`. Introduce `h k`. Rewrite using `[← h1, pushCh, MonoidHom.comp_apply, ← map_zpow (Units.map (g : R →* R'))]`.

Both sides reduce to the same expression. Use `⟨h1, ?_, ?_⟩` and prove the remaining obligations. Introduce `n y`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => rw [hz, map_zero, hz']`.

Consider the case `add a b ha hb => rw [hadd, map_add, ha, hb, map_add, hadd']`. Consider the case `single h r`. Rewrite using `[hs, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, hs', map_mul, he]`. Introduce `n v ψ γ`. Simplify using `only [GFrame.oEl, map_list_prod, List.map_ofFn]`.

Use `congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))` and prove the remaining obligations. Simplify using `[Function.comp_def, map_sub, MonoidAlgebra.mapRingHom_single, pushCh]`.
-/
theorem UpperTheory.V.Pa.BC.star_map :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing O'] [Algebra ℤ_[l] O'] (R R' : Type) [CommRing R] [Algebra O R] [CommRing R'] [Algebra O' R'] (g : R →+* R'), (∀ a : ℤ_[l], g (algebraMap O R (algebraMap ℤ_[l] O a)) = algebraMap O' R' (algebraMap ℤ_[l] O' a)) → (pushCh g (F.eps O R) = F.eps O' R') ∧ (∀ n y, MonoidAlgebra.mapRingHom F.G₀ g (F.star O R n y) = F.star O' R' n (MonoidAlgebra.mapRingHom F.G₀ g y)) ∧ ∀ (n : ℕ) (v : F.Vl) (ψ : Fin n → F.Gv v →* Rˣ) (γ : Fin n → F.Gv v), MonoidAlgebra.mapRingHom F.G₀ g (F.oEl v ψ γ) = F.oEl v (fun i => pushCh g (ψ i)) γ := by
  intro l _ F O O' _ _ _ _ R R' _ _ _ _ g hg
  have h1 : pushCh g (F.eps O R) = F.eps O' R' := by
    ext x
    simp [GFrame.eps, pushCh, hg]
  have hs : ∀ (S : Type) [CommRing S] [Algebra O S] (n : ℕ) (h : F.G₀) (r : S), F.star O S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O S h ^ (1 - (n : ℤ)) : Sˣ) : S)) := by
    intro S _ _ n h r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hs' : ∀ (S : Type) [CommRing S] [Algebra O' S] (n : ℕ) (h : F.G₀) (r : S), F.star O' S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O' S h ^ (1 - (n : ℤ)) : Sˣ) : S)) := by
    intro S _ _ n h r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hadd : ∀ (n : ℕ) (a b : MonoidAlgebra R F.G₀), F.star O R n (a + b) = F.star O R n a + F.star O R n b := by
    intro n a b
    simp [GFrame.star]
  have hadd' : ∀ (n : ℕ) (a b : MonoidAlgebra R' F.G₀), F.star O' R' n (a + b) = F.star O' R' n a + F.star O' R' n b := by
    intro n a b
    simp [GFrame.star]
  have hz : ∀ (n : ℕ), F.star O R n 0 = 0 := by
    intro n
    simp [GFrame.star]
  have hz' : ∀ (n : ℕ), F.star O' R' n 0 = 0 := by
    intro n
    simp [GFrame.star]
  have he : ∀ (h : F.G₀) (k : ℤ), g ((F.eps O R h ^ k : Rˣ) : R) = ((F.eps O' R' h ^ k : R'ˣ) : R') := by
    intro h k
    rw [← h1, pushCh, MonoidHom.comp_apply, ← map_zpow (Units.map (g : R →* R'))]
    rfl
  refine ⟨h1, ?_, ?_⟩
  · intro n y
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [hz, map_zero, hz']
    | add a b ha hb => rw [hadd, map_add, ha, hb, map_add, hadd']
    | single h r =>
      rw [hs, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, hs', map_mul, he]
  · intro n v ψ γ
    simp only [GFrame.oEl, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp [Function.comp_def, map_sub, MonoidAlgebra.mapRingHom_single, pushCh]
