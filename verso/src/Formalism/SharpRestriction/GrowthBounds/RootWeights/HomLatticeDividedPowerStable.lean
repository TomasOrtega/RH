import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionPreservesLattice

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section lat
variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

/- English proof (translation)
Establish `hres` using `restrictRepresentation_isRep E hE L hL`. Take `⟨s, π, h1, h2, h3, h4, h5⟩` from `weight_projections_exist (restrictRepresentation E L hL) hres`. Take `⟨s', π', h1', h2', h3', h4', h5'⟩` from `weight_projections_exist E hE`. Establish `hdec : f = ∑ mu' ∈ s', ∑ mu ∈ s, (π' mu' ∘ₗ f ∘ₗ π mu)`. Use extensionality with `x`.

Simplify using `only [LinearMap.sum_apply, LinearMap.comp_apply]`. Establish `: ∀ mu' ∈ s', ∑ mu ∈ s, π' mu' (f (π mu x)) = π' mu' (f x)`. Introduce `mu' _`. Rewrite using `[← map_sum, ← map_sum, h5]`. Rewrite using `[Finset.sum_congr rfl this, h5']`.

Establish `hwt : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ weightSp (homRepresentation (restrictRepresentation E L hL) E) (mu' - mu)`. Introduce `mu' mu`. Rewrite using `[mem_weightSp_iff_diagonal_apply]`. Introduce `c`. Use extensionality with `x`.

Simplify using `only [homRepresentation_apply, LinearMap.comp_apply, LinearMap.smul_apply, (mem_weightSp_iff_diagonal_apply E mu' _).1 (h4' mu' _) c, weightProjection_diagonal_apply_eq_smul _ hres mu (π mu) (h1 mu) c x, map_smul, Pi.sub_apply, Int.cast_sub, sub_smul, LinearMap.sub_apply]`. Establish `hcoe : ∀ mu, L.subtype ∘ₗ π mu = π' mu ∘ₗ L.subtype`. Introduce `mu`. Use `linearMap_ext_on_weightSpaces _ hres _ _ fun nu y hy => ?_` and prove the remaining obligations. Establish `hy' : (y : W) ∈ weightSp E nu` using `(restrict_mem_weightSpace_iff E L hL nu y).1 hy`.

Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply]`. Distinguish the cases in `h : nu = mu`. Substitute `h` using the available equality. Rewrite using `[(h1 nu).1 y hy, (h1' nu).1 _ hy']`. Rewrite using `[(h1 mu).2 nu h y hy, (h1' mu).2 nu h _ hy']`.

Both sides reduce to the same expression. Establish `hmem : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ homLattice M L`. Introduce `mu' mu x hx`. Establish `hx1 : ((π mu x : L) : W) ∈ M`. Use `congrArg (fun g : L →ₗ[KK O] W => g x) (hcoe mu)` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at this`. Rewrite using `[this]`. Conclude with `weightProjection_preserves_lattice E hE M hM mu (π' mu) (h1' mu) _ hx`. Conclude with `weightProjection_preserves_lattice E hE M hM mu' (π' mu') (h1' mu') _ (hf _ hx1)`. Rewrite using `[hdec, map_sum]`.

Use `Submodule.sum_mem _ fun mu' _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Submodule.sum_mem _ fun mu _ => ?_` and prove the remaining obligations. Rewrite using `[binomial_diagonal_apply_weight _ a (mu' - mu) _ (hwt mu' mu) k]`. Conclude with `int_smul_mem_lattice _ _ (hmem mu' mu)`.
-/
theorem homLattice_binomial_stable [CharZero (KK O)] [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W) (hE : IsGLRep E)
    (M : Submodule O W) (hM : UZStable (O := O) E M)
    (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a : Fin n) (k : ℕ)
    (f : L →ₗ[KK O] W) (hf : f ∈ homLattice M L) :
    binomE (homRepresentation (restrictRepresentation E L hL) E) a k f ∈ homLattice M L := by
  have hres := restrictRepresentation_isRep E hE L hL
  obtain ⟨s, π, h1, h2, h3, h4, h5⟩ := weight_projections_exist (restrictRepresentation E L hL) hres
  obtain ⟨s', π', h1', h2', h3', h4', h5'⟩ := weight_projections_exist E hE
  have hdec : f = ∑ mu' ∈ s', ∑ mu ∈ s, (π' mu' ∘ₗ f ∘ₗ π mu) := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    have : ∀ mu' ∈ s', ∑ mu ∈ s, π' mu' (f (π mu x)) = π' mu' (f x) := by
      intro mu' _
      rw [← map_sum, ← map_sum, h5]
    rw [Finset.sum_congr rfl this, h5']
  have hwt : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ weightSp (homRepresentation (restrictRepresentation E L hL) E) (mu' - mu) := by
    intro mu' mu
    rw [mem_weightSp_iff_diagonal_apply]
    intro c
    ext x
    simp only [homRepresentation_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      (mem_weightSp_iff_diagonal_apply E mu' _).1 (h4' mu' _) c, weightProjection_diagonal_apply_eq_smul _ hres mu (π mu) (h1 mu) c x, map_smul,
      Pi.sub_apply, Int.cast_sub, sub_smul, LinearMap.sub_apply]
  have hcoe : ∀ mu, L.subtype ∘ₗ π mu = π' mu ∘ₗ L.subtype := by
    intro mu
    refine linearMap_ext_on_weightSpaces _ hres _ _ fun nu y hy => ?_
    have hy' : (y : W) ∈ weightSp E nu := (restrict_mem_weightSpace_iff E L hL nu y).1 hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    by_cases h : nu = mu
    · subst h; rw [(h1 nu).1 y hy, (h1' nu).1 _ hy']
    · rw [(h1 mu).2 nu h y hy, (h1' mu).2 nu h _ hy']; rfl
  have hmem : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ homLattice M L := by
    intro mu' mu x hx
    have hx1 : ((π mu x : L) : W) ∈ M := by
      have := congrArg (fun g : L →ₗ[KK O] W => g x) (hcoe mu)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
      rw [this]
      exact weightProjection_preserves_lattice E hE M hM mu (π' mu) (h1' mu) _ hx
    exact weightProjection_preserves_lattice E hE M hM mu' (π' mu') (h1' mu') _ (hf _ hx1)
  rw [hdec, map_sum]
  refine Submodule.sum_mem _ fun mu' _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun mu _ => ?_
  rw [binomial_diagonal_apply_weight _ a (mu' - mu) _ (hwt mu' mu) k]
  exact int_smul_mem_lattice _ _ (hmem mu' mu)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hf i`. Conclude with `hf (b i) (hbM i)`. Introduce `hf show ∀ x : L, (x : W) ∈ M → f x ∈ M`. Introduce `x hx`.

Use `choose o ho using hbc x hx`. Establish `hx' : x = ∑ i, b.coord i x • b i`. Simplify using `only [Module.Basis.coord_apply]`. Conclude with `(b.sum_repr x).symm`. Rewrite using `[hx', map_sum]`.

Use `M.sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ho i, algebraMap_smul]`. Conclude with `M.smul_mem (o i) (hf i)`.
-/
theorem mem_homLattice_iff_basis (M : Submodule O W) (L : Submodule (KK O) W) {d : ℕ} (b : Module.Basis (Fin d) (KK O) L)
    (hbM : ∀ i, ((b i : L) : W) ∈ M)
    (hbc : ∀ x : L, (x : W) ∈ M → ∀ i, ∃ o : O, b.coord i x = algebraMap O (KK O) o) (f : L →ₗ[KK O] W) :
    f ∈ homLattice M L ↔ ∀ i, f (b i) ∈ M := by
  constructor
  · intro hf i
    exact hf (b i) (hbM i)
  · intro hf
    show ∀ x : L, (x : W) ∈ M → f x ∈ M
    intro x hx
    choose o ho using hbc x hx
    have hx' : x = ∑ i, b.coord i x • b i := by
      simp only [Module.Basis.coord_apply]
      exact (b.sum_repr x).symm
    rw [hx', map_sum]
    refine M.sum_mem fun i _ => ?_
    rw [map_smul, ho i, algebraMap_smul]
    exact M.smul_mem (o i) (hf i)

end lat

/- English proof (translation)
Introduce `O _ _ _ _ n W _ _ _ _ _ E hE M hM hMQ L hL`. Take `⟨d, b, hbM, hbc⟩` from `lattice_adapted_basis_exists O W M hM.2 hMQ L`. Establish `hiff` using `mem_homLattice_iff_basis M L b hbM hbc`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `u (⟨a, c, k, hac, rfl⟩ | ⟨a, k, rfl⟩) f hf`.

Conclude with `homLattice_dividedPower_stable E M hM.1 L hL a c hac k f hf`. Conclude with `homLattice_binomial_stable E hE M hM.1 L hL a k f hf`. Establish `: homLattice M L = (Submodule.pi Set.univ fun _ : Fin d => M).map ((b.constr (KK O)).toLinearMap.restrictScalars O)`. Use extensionality with `f`. Rewrite using `[hiff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hf`. Conclude with `⟨fun i => f (b i), fun i _ => hf i, b.constr_self (KK O) f⟩`. Introduce and unpack `⟨y, hy, rfl⟩ i`. Establish `: (b.constr (KK O) y) (b i) = y i` using `b.constr_basis (KK O) y i`.

Simplify `hy i trivial` using `[this]`. Rewrite using `[this]`. Conclude with `(Submodule.fg_pi fun _ => hM.2).map _`. Rewrite using `[eq_top_iff]`. Introduce `f _`.

Use `choose a ha hax using fun i => exists_clear_denominators_alt M (f (b i)) (by rw [hMQ]; trivial)`. Establish `hA : (∏ i, a i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => ha i`. Establish `hA1 : algebraMap O (KK O) (∏ i, a i) ≠ 0`. Simplify using `using (IsFractionRing.injective O (KK O)).ne hA`. Establish `h1 : (∏ i, a i) • f ∈ homLattice M L`.

Rewrite using `[hiff]`. Introduce `i`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem a (Finset.mem_univ i)`. Rewrite using `[LinearMap.smul_apply, hc, mul_comm, mul_smul]`. Conclude with `M.smul_mem _ (hax i)`.

Establish `h2 : f = (algebraMap O (KK O) (∏ i, a i))⁻¹ • ((∏ i, a i) • f)`. Rewrite using `[← algebraMap_smul (KK O) (∏ i, a i) f, smul_smul, inv_mul_cancel₀ hA1, one_smul]`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h1)`.
-/
theorem hom_lattice_dividedPower_stable : HomLatticeDividedPowerStable := by
  intro O _ _ _ _ n W _ _ _ _ _ E hE M hM hMQ L hL
  obtain ⟨d, b, hbM, hbc⟩ := lattice_adapted_basis_exists O W M hM.2 hMQ L
  have hiff := mem_homLattice_iff_basis M L b hbM hbc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro u (⟨a, c, k, hac, rfl⟩ | ⟨a, k, rfl⟩) f hf
    · exact homLattice_dividedPower_stable E M hM.1 L hL a c hac k f hf
    · exact homLattice_binomial_stable E hE M hM.1 L hL a k f hf
  · have : homLattice M L = (Submodule.pi Set.univ fun _ : Fin d => M).map
        ((b.constr (KK O)).toLinearMap.restrictScalars O) := by
      ext f
      rw [hiff]
      constructor
      · intro hf
        exact ⟨fun i => f (b i), fun i _ => hf i, b.constr_self (KK O) f⟩
      · rintro ⟨y, hy, rfl⟩ i
        have : (b.constr (KK O) y) (b i) = y i := b.constr_basis (KK O) y i
        simpa [this] using hy i trivial
    rw [this]
    exact (Submodule.fg_pi fun _ => hM.2).map _
  · rw [eq_top_iff]
    intro f _
    choose a ha hax using fun i => exists_clear_denominators_alt M (f (b i)) (by rw [hMQ]; trivial)
    have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ha i
    have hA1 : algebraMap O (KK O) (∏ i, a i) ≠ 0 := by
      simpa using (IsFractionRing.injective O (KK O)).ne hA
    have h1 : (∏ i, a i) • f ∈ homLattice M L := by
      rw [hiff]
      intro i
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
      rw [LinearMap.smul_apply, hc, mul_comm, mul_smul]
      exact M.smul_mem _ (hax i)
    have h2 : f = (algebraMap O (KK O) (∏ i, a i))⁻¹ • ((∏ i, a i) • f) := by
      rw [← algebraMap_smul (KK O) (∏ i, a i) f, smul_smul, inv_mul_cancel₀ hA1, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end Formalism.MainNotions.G.GLWeightTheory
