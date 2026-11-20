import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(AdicCompletion.map I f x).val n = 0`. Rewrite using `[AdicCompletion.map_val_apply]`. Express the relevant statement in the definitionally equal form `(f.reduceModIdeal (I ^ n)) (AdicCompletion.eval I M n x) = 0`. Rewrite using `[h, map_zero]`.
-/
private theorem ev_map {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (n : ℕ) (x : AdicCompletion I M) (h : AdicCompletion.eval I M n x = 0) :
    AdicCompletion.eval I M n (AdicCompletion.map I f x) = 0 := by
  change (AdicCompletion.map I f x).val n = 0
  rw [AdicCompletion.map_val_apply]
  change (f.reduceModIdeal (I ^ n)) (AdicCompletion.eval I M n x) = 0
  rw [h, map_zero]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `x.val n = 0`. Rewrite using `[← x.property (Nat.le_succ n)]`. Express the relevant statement in the definitionally equal form `(AdicCompletion.transitionMap I M (Nat.le_succ n)) (AdicCompletion.eval I M (n + 1) x) = 0`. Rewrite using `[h, map_zero]`.
-/
private theorem ev_succ {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (n : ℕ) (x : AdicCompletion I M) (h : AdicCompletion.eval I M (n + 1) x = 0) :
    AdicCompletion.eval I M n x = 0 := by
  change x.val n = 0
  rw [← x.property (Nat.le_succ n)]
  change (AdicCompletion.transitionMap I M (Nat.le_succ n)) (AdicCompletion.eval I M (n + 1) x) = 0
  rw [h, map_zero]

/- English proof (translation)
Take `⟨y, hy⟩` from `Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M 0 x)`. Rewrite using `[← hy, Submodule.Quotient.mk_eq_zero]`. Simplify using the standard rewrite rules.
-/
private theorem ev_zero {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (x : AdicCompletion I M) : AdicCompletion.eval I M 0 x = 0 := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M 0 x)
  rw [← hy, Submodule.Quotient.mk_eq_zero]
  simp

/- English proof (translation)
Rewrite using `[map_smul]`. Take `⟨y, hy⟩` from `Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M n x)`. Rewrite using `[← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.smul_mem_smul hc Submodule.mem_top`.
-/
private theorem ev_smul {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    (n : ℕ) (c : R) (hc : c ∈ I ^ n) (x : AdicCompletion I M) : AdicCompletion.eval I M n (c • x) = 0 := by
  rw [map_smul]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M n x)
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

/- English proof (translation)
Establish `hl : (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap = (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)).toIntLinearMap ∘ₗ (MonoidHom.toAdditive (Units.map φ.toMonoidHom)).toIntLinearMap`. Use extensionality with `u`. Conclude with `h _`. Express the relevant statement in the definitionally equal form `AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l] (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap) x = AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l] (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)).toIntLinearMap) (AdicCompletion.map (idl l) (LinearM …`. Rewrite using `[AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp, hl]`.
-/
private theorem kmap_comp (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ χ : X.K ≃+* X.K) (h : ∀ f, χ f = ψ (φ f))
    (x : X.Khat l) : X.kmap l χ x = X.kmap l ψ (X.kmap l φ x) := by
  have hl : (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap =
      (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)).toIntLinearMap ∘ₗ
        (MonoidHom.toAdditive (Units.map φ.toMonoidHom)).toIntLinearMap := by
    ext u
    exact h _
  change AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap) x =
    AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)).toIntLinearMap)
      (AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
        (MonoidHom.toAdditive (Units.map φ.toMonoidHom)).toIntLinearMap) x)
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp, hl]

/- English proof (translation)
Establish `hl : (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap = LinearMap.id`. Use extensionality with `u`. Conclude with `h _`. Express the relevant statement in the definitionally equal form `AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l] (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap) x = x`. Rewrite using `[hl, LinearMap.baseChange_id, AdicCompletion.map_id]`.

Both sides reduce to the same expression.
-/
private theorem kmap_id (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (χ : X.K ≃+* X.K) (h : ∀ f, χ f = f)
    (x : X.Khat l) : X.kmap l χ x = x := by
  have hl : (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap = LinearMap.id := by
    ext u
    exact h _
  change AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
      (MonoidHom.toAdditive (Units.map χ.toMonoidHom)).toIntLinearMap) x = x
  rw [hl, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

/- English proof (translation)
Introduce `Ω _ _ _ ε X l _ n`. Use `⟨⟨fun a u => ?_, fun {a b} hab u => ?_, fun {a b c} hab hbc u => ?_⟩, fun a b a' b' h h' => ⟨fun u => ?_, fun u => ?_⟩, fun k a b h u => ?_, fun ι S a b h u => ?_, fun k k' a hk => ?_, fun m a b h u => ?_, fun s a b h u => ?_, fun a b h u => ev_succ _ _ _ (h u), fun a b u => ev_z …` and prove the remaining obligations. Rewrite using `[sub_self, map_zero]`. Rewrite using `[← neg_sub, map_neg, hab u, neg_zero]`. Rewrite using `[← sub_add_sub_cancel (a u) (b u) (c u), map_add, hab u, hbc u, add_zero]`.

Rewrite using `[Pi.add_apply, Pi.add_apply, add_sub_add_comm, map_add, h u, h' u, add_zero]`. Rewrite using `[Pi.sub_apply, Pi.sub_apply, sub_sub_sub_comm, map_sub, h u, h' u, sub_zero]`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, ← smul_sub, map_smul, h u, smul_zero]`. Rewrite using `[Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib, map_sum]`. Conclude with `Finset.sum_eq_zero (fun i hi => h i hi u)`.

Rewrite using `[← sub_smul]`. Apply `ev_smul` to reduce the goal to its premises. Rewrite using `[idl, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `hk`. Simplify using `only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]`.

Rewrite using `[← map_sub]`. Conclude with `ev_map (idl l) _ n _ (h _)`. Simplify using `only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[← map_sub]`. Conclude with `ev_map (idl l) _ n _ (h _)`.

Use function extensionality and compare the values at `u`. Simplify using `only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`. Establish `hst : (s * t).toRingEquiv = s.toRingEquiv * t.toRingEquiv` using `rfl`. Rewrite using `[hst, map_mul, Units.val_mul, show ((cyclotomicCharacter Ω l) s.toRingEquiv : ℤ_[l]) * ((cyclotomicCharacter Ω l) t.toRingEquiv) * u 1 = ((cyclotomicCharacter Ω l) t.toRingEquiv) * (((cyclotomicCharacter Ω l) s.toRingEquiv) * u 1) by ring]`. Conclude with `kmap_comp X l _ _ _ (GlobalTheory.K4.gal_mul_apply X s t) _`.

Use function extensionality and compare the values at `u`. Simplify using `only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]`. Establish `h1 : (AlgEquiv.toRingEquiv (1 : Gal(Ω/ℚ))) = 1` using `rfl`. Establish `hu : ![u 0, u 1] = u`. Use extensionality with `i`.

Apply the tactic sequence `fin_cases i <;> rfl`. Rewrite using `[h1, map_one, Units.val_one, one_mul, hu]`. Conclude with `kmap_id X l _ (GlobalTheory.K4.gal_one_apply X) _`.
-/
theorem sApi : SApi := by
  intro Ω _ _ _ ε X l _ n
  refine ⟨⟨fun a u => ?_, fun {a b} hab u => ?_, fun {a b c} hab hbc u => ?_⟩,
    fun a b a' b' h h' => ⟨fun u => ?_, fun u => ?_⟩, fun k a b h u => ?_,
    fun ι S a b h u => ?_, fun k k' a hk => ?_, fun m a b h u => ?_, fun s a b h u => ?_,
    fun a b h u => ev_succ _ _ _ (h u), fun a b u => ev_zero _ _, fun s t a => ?_, fun a => ?_⟩
  · rw [sub_self, map_zero]
  · rw [← neg_sub, map_neg, hab u, neg_zero]
  · rw [← sub_add_sub_cancel (a u) (b u) (c u), map_add, hab u, hbc u, add_zero]
  · rw [Pi.add_apply, Pi.add_apply, add_sub_add_comm, map_add, h u, h' u, add_zero]
  · rw [Pi.sub_apply, Pi.sub_apply, sub_sub_sub_comm, map_sub, h u, h' u, sub_zero]
  · rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, map_smul, h u, smul_zero]
  · rw [Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib, map_sum]
    exact Finset.sum_eq_zero (fun i hi => h i hi u)
  · rw [← sub_smul]
    apply ev_smul
    rw [idl, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hk
  · simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← map_sub]
    exact ev_map (idl l) _ n _ (h _)
  · simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← map_sub]
    exact ev_map (idl l) _ n _ (h _)
  · funext u
    simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    have hst : (s * t).toRingEquiv = s.toRingEquiv * t.toRingEquiv := rfl
    rw [hst, map_mul, Units.val_mul,
      show ((cyclotomicCharacter Ω l) s.toRingEquiv : ℤ_[l]) * ((cyclotomicCharacter Ω l) t.toRingEquiv) * u 1 =
        ((cyclotomicCharacter Ω l) t.toRingEquiv) * (((cyclotomicCharacter Ω l) s.toRingEquiv) * u 1) by ring]
    exact kmap_comp X l _ _ _ (GlobalTheory.K4.gal_mul_apply X s t) _
  · funext u
    simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : (AlgEquiv.toRingEquiv (1 : Gal(Ω/ℚ))) = 1 := rfl
    have hu : ![u 0, u 1] = u := by
      ext i
      fin_cases i <;> rfl
    rw [h1, map_one, Units.val_one, one_mul, hu]
    exact kmap_id X l _ (GlobalTheory.K4.gal_one_apply X) _

end UpperTheory.V.Z.Kato.Nb

end
