import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsMin2IffFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraintsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

/- English proof (translation)
Introduce `O _ _ _ _ bar X _ _ _ _ ι _ a m u hsym hpsd`. Use `choose F hF using fun i => isMin2_iff_finite X m u (a i) hpsd`. Set `A : Set (Fin m → ℤ)` to `⋃ i, (fun (x : X) (k : Fin m) => u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) '' (F i : Set X)`. Set `V : Set (Fin m → ℤ)` to `Set.range fun (p : O × X × X) (k : Fin m) => u k (p.1 • p.2.1) p.2.2 - u k p.2.1 (bar p.1 • p.2.2)`. Establish `hA : A.Finite` using `Set.finite_iUnion fun i => (F i).finite_toSet.image _`.

Take `⟨r, v, hv, -⟩` from `GlobalTheory.T.minkowskiWeyl_orthant_cone_integral_constraints m A V hA`. Establish `hval : ∀ (t : Fin m → ℝ) (y z : X), (∑ k, t k • toReal (u k)) y z = ∑ k, t k * (u k y z : ℝ)` using `fun t y z => by simp [LinearMap.sum_apply]`. Establish `hdiff : ∀ (t : Fin m → ℝ) (p p' q q' : X), ∑ k, (((u k p p' - u k q q' : ℤ)) : ℝ) * t k = (∑ k, t k • toReal (u k)) p p' - (∑ k, t k • toReal (u k)) q q'` using `fun t p p' q q' => by`. Rewrite using `[hval, hval, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by push_cast; ring`.

Establish `hAiff : ∀ t : Fin m → ℝ, (∀ k, 0 ≤ t k) → ((∀ i, IsMin2 (∑ k, t k • toReal (u k)) (a i)) ↔ ∀ b ∈ A, ∑ k, (b k : ℝ) * t k ≤ 0)` using `fun t ht => by`. Prove the components needed by the constructor for the conclusion. Introduce `h b hb`. Choose the witnesses or unpack the hypotheses as in `⟨i, x, -, rfl⟩ : ∃ i, ∃ x ∈ (F i : Set X), (fun k : Fin m => u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) = b := by`. Simplify `hb` using `[A]`.

Rewrite using `[hdiff]`. Combine the linear relations using `[h i x]`. Introduce `h i`. Use `(hF i _ ⟨t, ht, rfl⟩).2 fun x hx => ?_` and prove the remaining obligations. Use `h _ (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)` as an intermediate fact.

Rewrite `this` using `[hdiff]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hViff : ∀ t : Fin m → ℝ, (∀ (c : O) (y z : X), (∑ k, t k • toReal (u k)) (c • y) z = (∑ k, t k • toReal (u k)) y (bar c • z)) ↔ ∀ b ∈ V, ∑ k, (b k : ℝ) * t k = 0` using `fun t => by`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h _ ⟨⟨c, y, z⟩, rfl⟩`.

Simplify using `only []`. Rewrite using `[hdiff, h, sub_self]`. Introduce `h c y z`. Use `h _ ⟨(c, y, z), rfl⟩` as an intermediate fact. Simplify using `only [] at this`.

Rewrite `this` using `[hdiff]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `γ : Fin r → LinearMap.BilinForm ℤ X` to `fun s => ∑ k, v s k • u k`. Establish `hγ : ∀ s y z, γ s y z = ∑ k, (v s k : ℤ) * u k y z` using `fun s y z => by`. Simplify using `[γ, LinearMap.sum_apply]`.

Establish `hγr : ∀ s, toReal (γ s) = ∑ k, (v s k : ℝ) • toReal (u k)` using `fun s => LinearMap.ext₂ fun y z => by`. Rewrite using `[hval, toReal_apply, hγ]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hvs : ∀ s, (∀ k, (0 : ℝ) ≤ v s k) ∧ (∀ b ∈ A, ∑ k, (b k : ℝ) * (v s k : ℝ) ≤ 0) ∧ (∀ b ∈ V, ∑ k, (b k : ℝ) * (v s k : ℝ) = 0)` using `fun s => by`.

Use `(hv fun k => (v s k : ℝ)).2 ⟨Pi.single s 1, fun j => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : j = s`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.

Rewrite using `[Finset.sum_eq_single s (fun j _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]`. Simplify using the standard rewrite rules. Establish `hbal : ∀ s, γ s ∈ balForms bar X` using `fun s => by`. Use `mem_balForms.2 ⟨fun y z => ?_, fun c y z => ?_⟩` and prove the remaining obligations. Simplify using `only [hγ, hsym _ y z]`.

Use `(hViff _).2 (hvs s).2.2 c y z` as an intermediate fact. Rewrite `this` using `[← hγr]`. Simplify using `using this`. Establish `hnn : ∀ s y, 0 ≤ γ s y y` using `fun s y => by`. Rewrite using `[hγ]`.

Conclude with `Finset.sum_nonneg fun k _ => mul_nonneg (Int.natCast_nonneg _) (hpsd k y)`. Use `⟨r, γ, hbal, hnn, fun s => ⟨?_, fun i => ?_⟩, ?_⟩` and prove the remaining obligations. Simplify `hbal s) (by simpa using hnn s) (by simp)` using `using GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone O bar X 1 ![γ s] ![1] (by simpa`. Rewrite using `[hγr]`. Conclude with `(hAiff _ (hvs s).1).2 (hvs s).2.1 i`.

Introduce and unpack `_ hB ⟨t, ht, rfl⟩`. Establish `hre` using `mem_realForms_of_mem_psdCone hB.1`. Take `⟨c, hc, rfl⟩` from `(hv t).1 ⟨ht, (hAiff t ht).1 hB.2, (hViff t).1 hre.2⟩`. Use `⟨c, hc, LinearMap.ext₂ fun y z => ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, hγ, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]`. Use `push_cast`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem contact_inter_rcone_spanned : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι]
    (a : ι → X) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) →
    ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧
      (∀ i, toReal (γ i) ∈ contact bar a) ∧ ∀ B ∈ contact bar a, B ∈ rcone u → B ∈ rcone γ := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a m u hsym hpsd
  classical
  choose F hF using fun i => isMin2_iff_finite X m u (a i) hpsd
  let A : Set (Fin m → ℤ) := ⋃ i, (fun (x : X) (k : Fin m) =>
    u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) '' (F i : Set X)
  let V : Set (Fin m → ℤ) := Set.range fun (p : O × X × X) (k : Fin m) =>
    u k (p.1 • p.2.1) p.2.2 - u k p.2.1 (bar p.1 • p.2.2)
  have hA : A.Finite := Set.finite_iUnion fun i => (F i).finite_toSet.image _
  obtain ⟨r, v, hv, -⟩ := GlobalTheory.T.minkowskiWeyl_orthant_cone_integral_constraints m A V hA
  have hval : ∀ (t : Fin m → ℝ) (y z : X), (∑ k, t k • toReal (u k)) y z = ∑ k, t k * (u k y z : ℝ) :=
    fun t y z => by simp [LinearMap.sum_apply]
  have hdiff : ∀ (t : Fin m → ℝ) (p p' q q' : X), ∑ k, (((u k p p' - u k q q' : ℤ)) : ℝ) * t k =
      (∑ k, t k • toReal (u k)) p p' - (∑ k, t k • toReal (u k)) q q' := fun t p p' q q' => by
    rw [hval, hval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  have hAiff : ∀ t : Fin m → ℝ, (∀ k, 0 ≤ t k) → ((∀ i, IsMin2 (∑ k, t k • toReal (u k)) (a i)) ↔
      ∀ b ∈ A, ∑ k, (b k : ℝ) * t k ≤ 0) := fun t ht => by
    constructor
    · intro h b hb
      obtain ⟨i, x, -, rfl⟩ : ∃ i, ∃ x ∈ (F i : Set X), (fun k : Fin m =>
          u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) = b := by
        simpa [A] using hb
      rw [hdiff]
      linarith [h i x]
    · intro h i
      refine (hF i _ ⟨t, ht, rfl⟩).2 fun x hx => ?_
      have := h _ (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)
      rw [hdiff] at this
      linarith
  have hViff : ∀ t : Fin m → ℝ, (∀ (c : O) (y z : X), (∑ k, t k • toReal (u k)) (c • y) z =
      (∑ k, t k • toReal (u k)) y (bar c • z)) ↔ ∀ b ∈ V, ∑ k, (b k : ℝ) * t k = 0 := fun t => by
    constructor
    · rintro h _ ⟨⟨c, y, z⟩, rfl⟩
      simp only []
      rw [hdiff, h, sub_self]
    · intro h c y z
      have := h _ ⟨(c, y, z), rfl⟩
      simp only [] at this
      rw [hdiff] at this
      linarith
  let γ : Fin r → LinearMap.BilinForm ℤ X := fun s => ∑ k, v s k • u k
  have hγ : ∀ s y z, γ s y z = ∑ k, (v s k : ℤ) * u k y z := fun s y z => by
    simp [γ, LinearMap.sum_apply]
  have hγr : ∀ s, toReal (γ s) = ∑ k, (v s k : ℝ) • toReal (u k) := fun s => LinearMap.ext₂ fun y z => by
    rw [hval, toReal_apply, hγ]
    push_cast
    rfl
  have hvs : ∀ s, (∀ k, (0 : ℝ) ≤ v s k) ∧ (∀ b ∈ A, ∑ k, (b k : ℝ) * (v s k : ℝ) ≤ 0) ∧
      (∀ b ∈ V, ∑ k, (b k : ℝ) * (v s k : ℝ) = 0) := fun s => by
    refine (hv fun k => (v s k : ℝ)).2 ⟨Pi.single s 1, fun j => ?_, ?_⟩
    · by_cases h : j = s
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · rw [Finset.sum_eq_single s (fun j _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
      simp
  have hbal : ∀ s, γ s ∈ balForms bar X := fun s => by
    refine mem_balForms.2 ⟨fun y z => ?_, fun c y z => ?_⟩
    · simp only [hγ, hsym _ y z]
    · have := (hViff _).2 (hvs s).2.2 c y z
      rw [← hγr] at this
      simpa using this
  have hnn : ∀ s y, 0 ≤ γ s y y := fun s y => by
    rw [hγ]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Int.natCast_nonneg _) (hpsd k y)
  refine ⟨r, γ, hbal, hnn, fun s => ⟨?_, fun i => ?_⟩, ?_⟩
  · simpa using GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone O bar X 1 ![γ s] ![1] (by simpa using hbal s) (by simpa using hnn s) (by simp)
  · rw [hγr]
    exact (hAiff _ (hvs s).1).2 (hvs s).2.1 i
  · rintro _ hB ⟨t, ht, rfl⟩
    have hre := mem_realForms_of_mem_psdCone hB.1
    obtain ⟨c, hc, rfl⟩ := (hv t).1 ⟨ht, (hAiff t ht).1 hB.2, (hViff t).1 hre.2⟩
    refine ⟨c, hc, LinearMap.ext₂ fun y z => ?_⟩
    rw [hval]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, hγ, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.CompanionTheory.Ar.Fan
