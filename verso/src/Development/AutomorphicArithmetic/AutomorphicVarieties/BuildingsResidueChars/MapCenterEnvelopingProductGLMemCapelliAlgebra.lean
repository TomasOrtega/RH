import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CapelliAlgebraMapOfGlRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GlRelationsHasUniversalProperty

attribute [local instance 100] LieRing.ofAssociativeRing

open UpperTheory.V.Af.CuspFin in
/- English proof (translation)
Introduce `𝔤 _ _ ι _ n b h1 h2 A _ _ _ _ ψ z hz`. Take `⟨T, _, _, E, hE⟩` from `hasUniv_of_sum (UpperTheory.glRelations_hasUniversalProperty n) (UpperTheory.capelliAlgebra_map_of_glRelations n) ι`. Use `letI : Algebra ℝ T := Algebra.compHom T (algebraMap ℝ ℂ)`. Use `haveI : IsScalarTower ℝ ℂ T := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `l : 𝔤 →ₗ[ℝ] T` to `b.constr ℝ fun p => E p.1 p.2.1 p.2.2`.

Establish `hl : ∀ v i j, l (b (v, i, j)) = E v i j` using `fun v i j => b.constr_basis ℝ _ _`. Establish `hlie : ∀ x y, l ⁅x, y⁆ = l x * l y - l y * l x`. Establish `key : (LieModule.toEnd ℝ 𝔤 𝔤 : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] 𝔤).compr₂ l = (LinearMap.mul ℝ T).compl₁₂ l l - ((LinearMap.mul ℝ T).compl₁₂ l l).flip`. Use `LinearMap.ext_basis b b ?_` and prove the remaining obligations. Introduce and unpack `⟨v, i, j⟩ ⟨v', k, m⟩`.

Express the relevant statement in the definitionally equal form `l ⁅b (v, i, j), b (v', k, m)⁆ = l (b (v, i, j)) * l (b (v', k, m)) - l (b (v', k, m)) * l (b (v, i, j))`. Rewrite using `[hl, hl]`. Distinguish the cases in `hv : v = v'`. Substitute `hv` using the available equality. Rewrite using `[h1, hE.rel.1 v i j k m, map_sub]`.

Apply the tactic sequence `congr 1 <;> split_ifs <;> simp [hl]`. Rewrite using `[h2 v v' hv, map_zero, (hE.rel.2 v v' hv i j k m).eq, sub_self]`. Introduce `x y`. Conclude with `LinearMap.congr_fun₂ key x y`. Set `L : 𝔤 →ₗ⁅ℝ⁆ T` to `{ l with map_lie' := fun {x y} => hlie x y }`.

Set `f : UniversalEnvelopingAlgebra ℝ 𝔤 →ₐ[ℝ] T` to `UniversalEnvelopingAlgebra.lift ℝ L`. Establish `hf : ∀ v i j, f (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) = E v i j` using `fun v i j => by`. Rewrite using `[← hl]`. Conclude with `UniversalEnvelopingAlgebra.lift_ι_apply ℝ L _`. Establish `hcen : f z ∈ Subalgebra.center ℂ T`.

Rewrite using `[Subalgebra.mem_center_iff]`. Introduce `t`. Establish `ht : t ∈ Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j}` using `hE.gen ▸ Algebra.mem_top`. Use `(Algebra.commute_of_mem_adjoin_of_forall_mem_commute ht ?_).symm.eq` and prove the remaining obligations. Introduce and unpack `_ ⟨v, i, j, rfl⟩`.

Rewrite using `[← hf, Commute, SemiconjBy, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]`. Establish `hbr : ∀ x y : 𝔤, ψ (UniversalEnvelopingAlgebra.ι ℝ x) * ψ (UniversalEnvelopingAlgebra.ι ℝ y) - ψ (UniversalEnvelopingAlgebra.ι ℝ y) * ψ (UniversalEnvelopingAlgebra.ι ℝ x) = ψ (UniversalEnvelopingAlgebra.ι ℝ ⁅x, y⁆)` using `fun x y => by`. Rewrite using `[LieHom.map_lie, Ring.lie_def, map_sub, map_mul, map_mul]`. Establish `hrel : MultiRel fun v i j => ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))`. Use `⟨fun v i j k m => ?_, fun v v' hv i j k m => ?_⟩` and prove the remaining obligations.

Rewrite using `[hbr, h1, map_sub, map_sub]`. Apply the tactic sequence `congr 1 <;> split_ifs <;> simp`. Rewrite using `[Commute, SemiconjBy, ← sub_eq_zero, hbr, h2 v v' hv, map_zero, map_zero]`. Take `⟨ρ, hρ⟩` from `hE.univ A _ hrel`. Establish `hcomp : (ρ.restrictScalars ℝ).comp f = ψ`.

Apply `UniversalEnvelopingAlgebra.hom_ext` to reduce the goal to its premises. Use `LieHom.ext fun x => LinearMap.congr_fun (f := LieHom.toLinearMap _) (g := LieHom.toLinearMap _) (b.ext ?_) x` and prove the remaining obligations. Introduce and unpack `⟨v, i, j⟩`. Express the relevant statement in the definitionally equal form `ρ (f (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))) = ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))`. Rewrite using `[hf, hρ]`.

Establish `hψ : ψ z = ρ (f z)` using `by rw [← hcomp]; rfl`. Rewrite using `[hψ]`. Establish `hle : capAlg E ≤ (capAlg fun v i j => ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))).comap ρ`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, u, rfl⟩`.

Use `Algebra.subset_adjoin ⟨v, u, ?_⟩` and prove the remaining obligations. Use `(map_qdet ρ _ _).trans ?_` and prove the remaining obligations. Simplify using `only [hρ]`. Conclude with `hle (hE.centre hcen)`.
-/
theorem UpperTheory.map_center_envelopingProductGL_mem_capelliAlgebra :
    ∀ (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (ι : Type) [Fintype ι] (n : ℕ) (b : Module.Basis (ι × Fin n × Fin n) ℝ 𝔤), (∀ v i j k l, ⁅b (v, i, j), b (v, k, l)⁆ = (if j = k then b (v, i, l) else 0) - (if l = i then b (v, k, j) else 0)) → (∀ v v', v ≠ v' → ∀ i j k l, ⁅b (v, i, j), b (v', k, l)⁆ = 0) → ∀ (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (ψ : UniversalEnvelopingAlgebra ℝ 𝔤 →ₐ[ℝ] A), ∀ z ∈ Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ 𝔤), ψ z ∈ UpperTheory.V.Af.CuspFin.capAlg fun v i j => ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) := by
  intro 𝔤 _ _ ι _ n b h1 h2 A _ _ _ _ ψ z hz
  obtain ⟨T, _, _, E, hE⟩ := hasUniv_of_sum (UpperTheory.glRelations_hasUniversalProperty n) (UpperTheory.capelliAlgebra_map_of_glRelations n) ι
  letI : Algebra ℝ T := Algebra.compHom T (algebraMap ℝ ℂ)
  haveI : IsScalarTower ℝ ℂ T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let l : 𝔤 →ₗ[ℝ] T := b.constr ℝ fun p => E p.1 p.2.1 p.2.2
  have hl : ∀ v i j, l (b (v, i, j)) = E v i j := fun v i j => b.constr_basis ℝ _ _
  have hlie : ∀ x y, l ⁅x, y⁆ = l x * l y - l y * l x := by
    have key : (LieModule.toEnd ℝ 𝔤 𝔤 : 𝔤 →ₗ[ℝ] 𝔤 →ₗ[ℝ] 𝔤).compr₂ l =
        (LinearMap.mul ℝ T).compl₁₂ l l - ((LinearMap.mul ℝ T).compl₁₂ l l).flip := by
      refine LinearMap.ext_basis b b ?_
      rintro ⟨v, i, j⟩ ⟨v', k, m⟩
      change l ⁅b (v, i, j), b (v', k, m)⁆ =
        l (b (v, i, j)) * l (b (v', k, m)) - l (b (v', k, m)) * l (b (v, i, j))
      rw [hl, hl]
      by_cases hv : v = v'
      · subst hv
        rw [h1, hE.rel.1 v i j k m, map_sub]
        congr 1 <;> split_ifs <;> simp [hl]
      · rw [h2 v v' hv, map_zero, (hE.rel.2 v v' hv i j k m).eq, sub_self]
    intro x y
    exact LinearMap.congr_fun₂ key x y
  let L : 𝔤 →ₗ⁅ℝ⁆ T := { l with map_lie' := fun {x y} => hlie x y }
  let f : UniversalEnvelopingAlgebra ℝ 𝔤 →ₐ[ℝ] T := UniversalEnvelopingAlgebra.lift ℝ L
  have hf : ∀ v i j, f (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) = E v i j := fun v i j => by
    rw [← hl]
    exact UniversalEnvelopingAlgebra.lift_ι_apply ℝ L _
  have hcen : f z ∈ Subalgebra.center ℂ T := by
    rw [Subalgebra.mem_center_iff]
    intro t
    have ht : t ∈ Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j} := hE.gen ▸ Algebra.mem_top
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ht ?_).symm.eq
    rintro _ ⟨v, i, j, rfl⟩
    rw [← hf, Commute, SemiconjBy, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]
  have hbr : ∀ x y : 𝔤,
      ψ (UniversalEnvelopingAlgebra.ι ℝ x) * ψ (UniversalEnvelopingAlgebra.ι ℝ y) -
        ψ (UniversalEnvelopingAlgebra.ι ℝ y) * ψ (UniversalEnvelopingAlgebra.ι ℝ x) =
      ψ (UniversalEnvelopingAlgebra.ι ℝ ⁅x, y⁆) := fun x y => by
    rw [LieHom.map_lie, Ring.lie_def, map_sub, map_mul, map_mul]
  have hrel : MultiRel fun v i j => ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j))) := by
    refine ⟨fun v i j k m => ?_, fun v v' hv i j k m => ?_⟩
    · rw [hbr, h1, map_sub, map_sub]
      congr 1 <;> split_ifs <;> simp
    · rw [Commute, SemiconjBy, ← sub_eq_zero, hbr, h2 v v' hv, map_zero, map_zero]
  obtain ⟨ρ, hρ⟩ := hE.univ A _ hrel
  have hcomp : (ρ.restrictScalars ℝ).comp f = ψ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => LinearMap.congr_fun (f := LieHom.toLinearMap _)
      (g := LieHom.toLinearMap _) (b.ext ?_) x
    rintro ⟨v, i, j⟩
    change ρ (f (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))) =
      ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))
    rw [hf, hρ]
  have hψ : ψ z = ρ (f z) := by rw [← hcomp]; rfl
  rw [hψ]
  have hle : capAlg E ≤ (capAlg fun v i j =>
      ψ (UniversalEnvelopingAlgebra.ι ℝ (b (v, i, j)))).comap ρ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, u, rfl⟩
    refine Algebra.subset_adjoin ⟨v, u, ?_⟩
    refine (map_qdet ρ _ _).trans ?_
    simp only [hρ]
  exact hle (hE.centre hcen)
