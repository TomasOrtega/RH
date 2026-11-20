import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpannedOfCoverStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VorFunValueLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemConeOfModTwoLiftStatement

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

/- English proof (translation)
Introduce `O _ _ _ _ bar g hcov X _ _ _ _`. Use `haveI : Module.Finite ℤ X := Module.Finite.trans O X`. Take `⟨n, r, hr⟩` from `Module.Finite.exists_fin' ℤ X`. Take `⟨k, nP, P, hPs, hPp, hPc⟩` from `hcov X`. Establish `hcls : ∀ (j : Fin k) (y : Fin n → ZMod (1 + 1)), ∃ F : Finset (Fin n → ℤ), (∀ a ∈ F, redV 1 a = y) ∧ ∀ B ∈ rcone (P j), ∃ a ∈ F, ∀ a', redV 1 a' = y → B (r a) (r a) ≤ B (r a') (r a')`.

Introduce `j y`. Take `⟨F, hF⟩` from `GlobalTheory.dickson_finite_below_every (ι := {a : Fin n → ℤ // redV 1 a = y}) (nP j) fun a i => (P j i (r a.1) (r a.1)).toNat`. Use `⟨F.map (Function.Embedding.subtype _), fun a ha => ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, -, rfl⟩` from `Finset.mem_map.1 ha`. Conclude with `a.2`.

Introduce and unpack `B ⟨t, ht, rfl⟩`. Establish `hval : ∀ a : Fin n → ℤ, (∑ i, t i • toReal (P j i)) (r a) (r a) = ∑ i, t i * (P j i (r a) (r a) : ℝ)` using `fun a => by`. Simplify using `[LinearMap.sum_apply]`. Take `⟨a0, ha0, -⟩` from `hF ⟨_, (redV_surjective 1 n y).choose_spec⟩`. Take `⟨a1, ha1, hmin⟩` from `Finset.exists_min_image (F.map (Function.Embedding.subtype _)) (fun a => (∑ i, t i • toReal (P j i)) (r a) (r a)) ⟨_, Finset.mem_map_of_mem _ ha0⟩`.

Use `⟨a1, ha1, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨a', ha', hle⟩` from `hF ⟨a, ha⟩`. Use `(hmin _ (Finset.mem_map_of_mem _ ha')).trans ?_` and prove the remaining obligations. Simplify using `only [Function.Embedding.subtype_apply, hval]`. Use `Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)` and prove the remaining obligations.

Establish `h1` using `hle i`. Establish `h2` using `hPp j i (r a'.1)`. Establish `h3` using `hPp j i (r a)`. Simplify using `only at h1`. Conclude with `(by omega : P j i (r a'.1) (r a'.1) ≤ P j i (r a) (r a))` after adjusting the coercions.

Use `choose F hFred hFmin using hcls`. Establish `hred : ∀ (j : Fin k) (c : ∀ y, ↥(F j y)) (y : Fin n → ZMod (1 + 1)), redV 1 (c y).1 = y` using `fun j c y => hFred j y _ (c y).2`. Establish `cell : ∀ (j : Fin k) (c : ∀ y, ↥(F j y)), ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar (vorFun O g) γ ∧ (contact bar fun y => r (c y).1) ⊆ rcone γ`. Introduce `j c`. Establish `hcv` using `(vorFun_value_le O bar g X n r (fun y => (c y).1) hr (hred j c)).1`.

Take `⟨s, γ, h1, h2, h3, h4⟩` from `GlobalTheory.T.contact_set_spanned_of_cover O bar hcov X _ _ hcv`. Conclude with `⟨s, γ, GlobalTheory.T.isCell_vorFun_of_contact_subset_rcone O bar g X n r _ hr (hred j c) s γ h1 h2 h3 h4, h4⟩`. Use `choose s γ hγ hγc using cell`. Use `⟨⋃ j, ⋃ c, Set.range (γ j c), Set.finite_iUnion fun j => Set.finite_iUnion fun c => Set.finite_range _, fun B hB => ?_⟩` and prove the remaining obligations. Take `⟨e, j, c, hc0, hce⟩` from `hPc B hB`.

Establish `hB' : pullR e.toLinearMap B ∈ psdCone bar X` using `pullR_mem_psdCone e.surjective hB`. Establish `hBP : pullR e.toLinearMap B ∈ rcone (P j)` using `⟨c, hc0, hce⟩`. Use `choose a0 ha0F ha0 using fun y => hFmin j y _ hBP`. Set `d : ∀ y, ↥(F j y)` to `fun y => ⟨a0 y, ha0F y⟩`. Establish `hcon : pullR e.toLinearMap B ∈ contact bar fun y => r (d y).1`.

Use `⟨hB', fun y x => ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `hr x`. Establish `hb : redV 1 (a0 y + (b + b)) = y`. Establish `h2 : a0 y + (b + b) = a0 y + (((1 : ℕ) : ℤ) + 1) • b`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, redV_add_smul]`. Conclude with `hFred j y _ (ha0F y)`.

Simplify `ha0 y _ hb` using `only [map_add]`. Take `⟨c', hc', hBc⟩` from `hγc j d hcon`. Conclude with `⟨e, _, γ j d, c', hγ j d, fun i => Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨d, i, rfl⟩⟩, hc', hBc⟩`.
-/
theorem exists_vorFun_cells : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone bar X, ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar (vorFun O g) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro O _ _ _ _ bar g hcov X _ _ _ _
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' ℤ X
  obtain ⟨k, nP, P, hPs, hPp, hPc⟩ := hcov X
  have hcls : ∀ (j : Fin k) (y : Fin n → ZMod (1 + 1)), ∃ F : Finset (Fin n → ℤ), (∀ a ∈ F, redV 1 a = y) ∧
      ∀ B ∈ rcone (P j), ∃ a ∈ F, ∀ a', redV 1 a' = y → B (r a) (r a) ≤ B (r a') (r a') := by
    intro j y
    obtain ⟨F, hF⟩ := GlobalTheory.dickson_finite_below_every (ι := {a : Fin n → ℤ // redV 1 a = y}) (nP j)
      fun a i => (P j i (r a.1) (r a.1)).toNat
    refine ⟨F.map (Function.Embedding.subtype _), fun a ha => ?_, ?_⟩
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 ha
      exact a.2
    · rintro B ⟨t, ht, rfl⟩
      have hval : ∀ a : Fin n → ℤ, (∑ i, t i • toReal (P j i)) (r a) (r a) = ∑ i, t i * (P j i (r a) (r a) : ℝ) := fun a => by
        simp [LinearMap.sum_apply]
      obtain ⟨a0, ha0, -⟩ := hF ⟨_, (redV_surjective 1 n y).choose_spec⟩
      obtain ⟨a1, ha1, hmin⟩ := Finset.exists_min_image (F.map (Function.Embedding.subtype _))
        (fun a => (∑ i, t i • toReal (P j i)) (r a) (r a)) ⟨_, Finset.mem_map_of_mem _ ha0⟩
      refine ⟨a1, ha1, fun a ha => ?_⟩
      obtain ⟨a', ha', hle⟩ := hF ⟨a, ha⟩
      refine (hmin _ (Finset.mem_map_of_mem _ ha')).trans ?_
      simp only [Function.Embedding.subtype_apply, hval]
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
      have h1 := hle i
      have h2 := hPp j i (r a'.1)
      have h3 := hPp j i (r a)
      simp only at h1
      exact_mod_cast (by omega : P j i (r a'.1) (r a'.1) ≤ P j i (r a) (r a))
  choose F hFred hFmin using hcls
  have hred : ∀ (j : Fin k) (c : ∀ y, ↥(F j y)) (y : Fin n → ZMod (1 + 1)), redV 1 (c y).1 = y :=
    fun j c y => hFred j y _ (c y).2
  have cell : ∀ (j : Fin k) (c : ∀ y, ↥(F j y)), ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X),
      IsCell bar (vorFun O g) γ ∧ (contact bar fun y => r (c y).1) ⊆ rcone γ := by
    intro j c
    have hcv := (vorFun_value_le O bar g X n r (fun y => (c y).1) hr (hred j c)).1
    obtain ⟨s, γ, h1, h2, h3, h4⟩ := GlobalTheory.T.contact_set_spanned_of_cover O bar hcov X _ _ hcv
    exact ⟨s, γ, GlobalTheory.T.isCell_vorFun_of_contact_subset_rcone O bar g X n r _ hr (hred j c) s γ h1 h2 h3 h4, h4⟩
  choose s γ hγ hγc using cell
  refine ⟨⋃ j, ⋃ c, Set.range (γ j c), Set.finite_iUnion fun j => Set.finite_iUnion fun c => Set.finite_range _,
    fun B hB => ?_⟩
  obtain ⟨e, j, c, hc0, hce⟩ := hPc B hB
  have hB' : pullR e.toLinearMap B ∈ psdCone bar X := pullR_mem_psdCone e.surjective hB
  have hBP : pullR e.toLinearMap B ∈ rcone (P j) := ⟨c, hc0, hce⟩
  choose a0 ha0F ha0 using fun y => hFmin j y _ hBP
  let d : ∀ y, ↥(F j y) := fun y => ⟨a0 y, ha0F y⟩
  have hcon : pullR e.toLinearMap B ∈ contact bar fun y => r (d y).1 := by
    refine ⟨hB', fun y x => ?_⟩
    obtain ⟨b, rfl⟩ := hr x
    have hb : redV 1 (a0 y + (b + b)) = y := by
      have h2 : a0 y + (b + b) = a0 y + (((1 : ℕ) : ℤ) + 1) • b := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [h2, redV_add_smul]
      exact hFred j y _ (ha0F y)
    simpa only [map_add] using ha0 y _ hb
  obtain ⟨c', hc', hBc⟩ := hγc j d hcon
  exact ⟨e, _, γ j d, c', hγ j d, fun i => Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨d, i, rfl⟩⟩, hc', hBc⟩

end GlobalTheory.CompanionTheory.Ar.Fan
