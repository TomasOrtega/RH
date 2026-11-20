import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FiniteOfTorsion

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g g' : ℕ} {Λ Λ' : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] {Ψ : Type} [Fintype Ψ]
  (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))

/- English proof (translation)
Establish `h4 : ∀ v, ∃ v', R'.P v' = φ (R.P v)` using `fun v => by`. Establish `h : φ (R.P v) ∈ Set.range R'.P` using `h1 ▸ ⟨_, ⟨v, rfl⟩, rfl⟩`. Conclude with `h`. Use `choose f hf using h4`. Set `α : Λ →ₗ[𝓞 E] Λ'` to `{ toFun := f map_add' := fun v w => precomp_injective R' (by rw [map_add, hf, hf, hf, map_add, map_add]) map_smul' := fun a v => precomp_injective R' (by rw [RingHom.id_apply, R'.act, hf, hf, R.act, h3]) }`.

Use `⟨LinearEquiv.ofBijective α ⟨fun v w h => ?_, fun v' => ?_⟩, hf⟩` and prove the remaining obligations. Establish `h' : f v = f w` using `h`. Conclude with `precomp_injective R (φ.injective (by rw [← hf, ← hf, h']))`. Establish `h : R'.P v' ∈ φ '' Set.range R.P` using `h1.symm ▸ ⟨v', rfl⟩`. Take `⟨_, ⟨v, rfl⟩, hv⟩` from `h`.

Conclude with `⟨v, precomp_injective R' ((hf v).trans hv)⟩`.
-/
theorem exists_equiv (h1 : φ '' Set.range R.P = Set.range R'.P) (h3 : ∀ a x, φ (R.B a x) = R'.B a (φ x)) :
    ∃ α : Λ ≃ₗ[𝓞 E] Λ', ∀ v, R'.P (α v) = φ (R.P v) := by
  have h4 : ∀ v, ∃ v', R'.P v' = φ (R.P v) := fun v => by
    have h : φ (R.P v) ∈ Set.range R'.P := h1 ▸ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact h
  choose f hf using h4
  let α : Λ →ₗ[𝓞 E] Λ' :=
    { toFun := f
      map_add' := fun v w => precomp_injective R' (by rw [map_add, hf, hf, hf, map_add, map_add])
      map_smul' := fun a v => precomp_injective R' (by rw [RingHom.id_apply, R'.act, hf, hf, R.act, h3]) }
  refine ⟨LinearEquiv.ofBijective α ⟨fun v w h => ?_, fun v' => ?_⟩, hf⟩
  · have h' : f v = f w := h
    exact precomp_injective R (φ.injective (by rw [← hf, ← hf, h']))
  · have h : R'.P v' ∈ φ '' Set.range R.P := h1.symm ▸ ⟨v', rfl⟩
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := h
    exact ⟨v, precomp_injective R' ((hf v).trans hv)⟩

/- English proof (translation)
Simplify using `only [proj_apply, map_sum, map_smul, h3]`.
-/
theorem proj_equiv (h3 : ∀ a x, φ (R.B a x) = R'.B a (φ x)) (s : 𝓞 E →+* ℂ) (x : Fin g → ℂ) :
    proj R'.B s (φ x) = φ (proj R.B s x) := by
  simp only [proj_apply, map_sum, map_smul, h3]

/- English proof (translation)
Distinguish the cases in `hI : I = ⊥`. Substitute `hI` using the available equality. Rewrite using `[Submodule.map_bot, RiemLat.nz, RiemLat.nz, dif_neg, dif_neg]`. Introduce and unpack `⟨r, v, h1, h4, h5, -⟩`. Conclude with `h5.ne_zero ⟨0, h1⟩ (h4 _)`.

Introduce and unpack `⟨r, v, h1, h4, h5, -⟩`. Conclude with `h5.ne_zero ⟨0, h1⟩ (h4 _)`. Use `R.free` as an intermediate fact. Use `R.fin` as an intermediate fact. Take `⟨r, v, hv⟩` from `exists_family hI`.

Establish `h4 : (Submodule.span (𝓞 E) (Set.range fun a => α (v a))).toAddSubgroup.relIndex (I.map α.toLinearMap).toAddSubgroup = (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup`. Rewrite using `[← relIndex_map α.toLinearMap α.injective, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hw : IsNzFamily (I.map α.toLinearMap) r fun a => α (v a)` using `⟨hv.1, fun a => Submodule.mem_map_of_mem (hv.2.1 a), hv.2.2.1.map' α.toLinearMap α.ker, h4 ▸ hv.2.2.2⟩`. Rewrite using `[nz_eq R hσ hv, nz_eq R' hσ hw, RiemLat.nzOf, RiemLat.nzOf, h4]`.

Simplify using `only [RiemLat.gram, eigComp_eq, hα, proj_equiv R R' φ h3, h2]`.
-/
theorem nz_map {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (h2 : ∀ x y, R'.ip (φ x) (φ y) = R.ip x y)
    (h3 : ∀ a x, φ (R.B a x) = R'.B a (φ x)) (α : Λ ≃ₗ[𝓞 E] Λ') (hα : ∀ v, R'.P (α v) = φ (R.P v))
    (I : Submodule (𝓞 E) Λ) : R'.nz σ (I.map α.toLinearMap) = R.nz σ I := by
  by_cases hI : I = ⊥
  · subst hI
    rw [Submodule.map_bot, RiemLat.nz, RiemLat.nz, dif_neg, dif_neg]
    · rintro ⟨r, v, h1, h4, h5, -⟩
      exact h5.ne_zero ⟨0, h1⟩ (h4 _)
    · rintro ⟨r, v, h1, h4, h5, -⟩
      exact h5.ne_zero ⟨0, h1⟩ (h4 _)
  have := R.free
  have := R.fin
  obtain ⟨r, v, hv⟩ := exists_family hI
  have h4 : (Submodule.span (𝓞 E) (Set.range fun a => α (v a))).toAddSubgroup.relIndex
      (I.map α.toLinearMap).toAddSubgroup =
      (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup := by
    rw [← relIndex_map α.toLinearMap α.injective, Submodule.map_span, ← Set.range_comp]
    rfl
  have hw : IsNzFamily (I.map α.toLinearMap) r fun a => α (v a) :=
    ⟨hv.1, fun a => Submodule.mem_map_of_mem (hv.2.1 a), hv.2.2.1.map' α.toLinearMap α.ker, h4 ▸ hv.2.2.2⟩
  rw [nz_eq R hσ hv, nz_eq R' hσ hw, RiemLat.nzOf, RiemLat.nzOf, h4]
  simp only [RiemLat.gram, eigComp_eq, hα, proj_equiv R R' φ h3, h2]

/- English proof (translation)
Establish `h4 : ∀ v w, R'.form (α v) (α w) = R.form v w` using `fun v w => by`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Rewrite using `[← imB_P, ← imB_P, imB_apply, imB_apply, hα, hα, h2]`. Establish `h5 : ∀ v, α v ∈ I.map α.toLinearMap ↔ v ∈ I` using `fun v => ⟨fun ⟨w, hw, h⟩ => α.injective h ▸ hw, fun h => Submodule.mem_map_of_mem h⟩`. Use `and_congr (by simp) (and_congr ?_ ?_)` and prove the remaining obligations.

Unfold `IsSaturated`. Rewrite using `[α.surjective.forall]`. Simplify using `only [← map_zsmul, h5]`. Unfold `IsIsoSub`. Rewrite using `[α.surjective.forall]`.

Use `forall_congr' fun v => imp_congr (h5 v) ?_` and prove the remaining obligations. Rewrite using `[α.surjective.forall]`. Simplify using `only [h4, h5]`.
-/
theorem isCusp_map (h2 : ∀ x y, R'.ip (φ x) (φ y) = R.ip x y) (α : Λ ≃ₗ[𝓞 E] Λ')
    (hα : ∀ v, R'.P (α v) = φ (R.P v)) (I : Submodule (𝓞 E) Λ) :
    R'.IsCusp (I.map α.toLinearMap) ↔ R.IsCusp I := by
  have h4 : ∀ v w, R'.form (α v) (α w) = R.form v w := fun v w => by
    apply Int.cast_injective (α := ℝ)
    rw [← imB_P, ← imB_P, imB_apply, imB_apply, hα, hα, h2]
  have h5 : ∀ v, α v ∈ I.map α.toLinearMap ↔ v ∈ I := fun v =>
    ⟨fun ⟨w, hw, h⟩ => α.injective h ▸ hw, fun h => Submodule.mem_map_of_mem h⟩
  refine and_congr (by simp) (and_congr ?_ ?_)
  · unfold IsSaturated
    rw [α.surjective.forall]
    simp only [← map_zsmul, h5]
  · unfold IsIsoSub
    rw [α.surjective.forall]
    refine forall_congr' fun v => imp_congr (h5 v) ?_
    rw [α.surjective.forall]
    simp only [h4, h5]

end

/- English proof (translation)
Introduce `E _ _ _ g Λ _ _ Ψ _ R σ g' Λ' _ _ R' φ hσ h1 h2 h3`. Take `⟨α, hα⟩` from `exists_equiv R R' φ h1 h3`. Use `⟨?_, ?_, fun m => forall_congr' fun τ => ?_, α, hα, fun I _ => nz_map R R' φ hσ h2 h3 α hα I⟩` and prove the remaining obligations. Unfold `RiemLat.cuspW`. Use `congr 2`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨I', hI, rfl⟩`. Take `⟨I, rfl⟩ : ∃ I : Submodule (𝓞 E) Λ, I.map α.toLinearMap = I'` from `⟨I'.comap α.toLinearMap, Submodule.map_comap_eq_of_surjective α.surjective I'⟩`. Conclude with `⟨I, (isCusp_map R R' φ h2 α hα I).1 hI, by rw [nz_map R R' φ hσ h2 h3 α hα]⟩`.

Introduce and unpack `⟨I, hI, rfl⟩`. Conclude with `⟨_, (isCusp_map R R' φ h2 α hα I).2 hI, by rw [nz_map R R' φ hσ h2 h3 α hα]⟩`. Unfold `RiemLat.lam1 RiemLat.normSq`. Use `congr 1`. Use extensionality with `x`.

Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[α.surjective.exists]`. Simplify using `only [hα, h2, ne_eq, α.map_eq_zero_iff]`. Establish `h4 : eigSp R'.B (σ τ) = (eigSp R.B (σ τ)).map φ.toLinearMap`. Use extensionality with `y`.

Take `⟨x, rfl⟩` from `φ.surjective y`. Rewrite using `[Submodule.mem_map_equiv, φ.symm_apply_apply, mem_eig, mem_eig]`. Simplify using `only [← h3, ← map_smul, φ.injective.eq_iff]`. Rewrite using `[h4, LinearEquiv.finrank_map_eq]`.
-/
theorem riemann_lattice_isometry_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (g' : ℕ) (Λ' : Type) [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R' : RiemLat E g' Λ') (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)), IsCMFam σ → φ '' Set.range R.P = Set.range R'.P → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) → (∀ a x, φ (R.B a x) = R'.B a (φ x)) → R'.cuspW σ = R.cuspW σ ∧ R'.lam1 = R.lam1 ∧ (∀ m, R'.HasRank σ m ↔ R.HasRank σ m) ∧ ∃ α : Λ ≃ₗ[𝓞 E] Λ', (∀ v, R'.P (α v) = φ (R.P v)) ∧ ∀ I, IsIsoSub R.form I → R'.nz σ (I.map α.toLinearMap) = R.nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ g' Λ' _ _ R' φ hσ h1 h2 h3
  obtain ⟨α, hα⟩ := exists_equiv R R' φ h1 h3
  refine ⟨?_, ?_, fun m => forall_congr' fun τ => ?_, α, hα, fun I _ => nz_map R R' φ hσ h2 h3 α hα I⟩
  · unfold RiemLat.cuspW
    congr 2
    ext x
    constructor
    · rintro ⟨I', hI, rfl⟩
      obtain ⟨I, rfl⟩ : ∃ I : Submodule (𝓞 E) Λ, I.map α.toLinearMap = I' :=
        ⟨I'.comap α.toLinearMap, Submodule.map_comap_eq_of_surjective α.surjective I'⟩
      exact ⟨I, (isCusp_map R R' φ h2 α hα I).1 hI, by rw [nz_map R R' φ hσ h2 h3 α hα]⟩
    · rintro ⟨I, hI, rfl⟩
      exact ⟨_, (isCusp_map R R' φ h2 α hα I).2 hI, by rw [nz_map R R' φ hσ h2 h3 α hα]⟩
  · unfold RiemLat.lam1 RiemLat.normSq
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    rw [α.surjective.exists]
    simp only [hα, h2, ne_eq, α.map_eq_zero_iff]
  · have h4 : eigSp R'.B (σ τ) = (eigSp R.B (σ τ)).map φ.toLinearMap := by
      ext y
      obtain ⟨x, rfl⟩ := φ.surjective y
      rw [Submodule.mem_map_equiv, φ.symm_apply_apply, mem_eig, mem_eig]
      simp only [← h3, ← map_smul, φ.injective.eq_iff]
    rw [h4, LinearEquiv.finrank_map_eq]

end LevelTowerAlt
