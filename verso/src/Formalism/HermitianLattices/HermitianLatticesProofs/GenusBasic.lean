import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[isomAct_mem_gmap]`. Use `first`. Consider the case `rfl`. Consider the case `simp`.

Consider the case `exact Iff.rfl`.
-/
theorem genusBasic_gmap_one (L : Submodule R V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  rw [isomAct_mem_gmap]
  first
  | rfl
  | simp
  | exact Iff.rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [isomAct_mem_gmap]`. Both sides reduce to the same expression.
-/
theorem genusBasic_gmap_mul (g₁ g₂ : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap (g₂ * g₁) L = gmap g₂ (gmap g₁ L) := by
  ext x
  simp only [isomAct_mem_gmap]
  rfl

/- English proof (translation)
Use `first`. Consider the case `exact isomAct_gmap_symm g L`. Consider the case `(ext x; simp only [isomAct_mem_gmap]; simp)`.
-/
theorem genusBasic_gmap_inv (g : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap g⁻¹ (gmap g L) = L := by
  first
  | exact isomAct_gmap_symm g L
  | (ext x; simp only [isomAct_mem_gmap]; simp)

/- English proof (translation)
Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem genusBasic_mem_one_mul (x : K) (hx : x ∈ (1 : Submodule R K)) (r : R) :
    algebraMap R K r * x ∈ (1 : Submodule R K) := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ r hx

/- English proof (translation)
Rewrite using `[← algebraMap_smul K r w, map_smul, smul_eq_mul]`.
-/
theorem genusBasic_hsmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (v w : V) :
    h v (r • w) = algebraMap R K r * h v w := by
  rw [← algebraMap_smul K r w, map_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, locBasic_sigma_spec, starRingEnd_apply]`.
-/
theorem genusBasic_hsmul_left (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (v w : V) :
    h (r • v) w = algebraMap R K (locBasic_sigma hinj hstar r) * h v w := by
  rw [← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    locBasic_sigma_spec, starRingEnd_apply]

/- English proof (translation)
Unfold `hcompl at hs ⊢`. Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨hx1, hx2⟩` from `hx`. Use `Submonoid.subset_closure (Set.mem_setOf.2 ⟨hx2 _ (locBasic_sigma_spec hinj hstar x), fun t ht => ?_⟩)` and prove the remaining obligations.

Establish `e : t = x` using `hinj (by rw [ht, locBasic_sigma_spec, star_star])`. Rewrite using `[e]`. Conclude with `hx1`. Consider the case `one => rw [map_one]`. Conclude with `Submonoid.one_mem _`.

Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `Submonoid.mul_mem _ hx hy`.
-/
theorem genusBasic_sigma_mem (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (s : R) (hs : s ∈ hcompl (K := K) p) :
    locBasic_sigma hinj hstar s ∈ hcompl (K := K) p := by
  unfold hcompl at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨hx1, hx2⟩ := hx
    refine Submonoid.subset_closure (Set.mem_setOf.2 ⟨hx2 _ (locBasic_sigma_spec hinj hstar x), fun t ht => ?_⟩)
    have e : t = x := hinj (by rw [ht, locBasic_sigma_spec, star_star])
    rw [e]
    exact hx1
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy

/- English proof (translation)
Use `haveI := hp.isPrime`. Conclude with `locBasic_hcompl_not_mem p s hs`.
-/
theorem genusBasic_hS (p : Ideal R) (hp : p.IsMaximal) (s : R) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p := by
  haveI := hp.isPrime
  exact locBasic_hcompl_not_mem p s hs

/- English proof (translation)
The claim follows from `locBasic_lg (fun p => hcompl (K := K) p) (fun p hp s hs => genusBasic_hS p hp s hs) L x hx`.
-/
theorem genusBasic_lg {W : Type*} [AddCommGroup W] [Module R W] (L : Submodule R W) (x : W)
    (hx : ∀ p : Ideal R, p.IsMaximal → x ∈ loc (K := K) p L) : x ∈ L := locBasic_lg (fun p => hcompl (K := K) p) (fun p hp s hs => genusBasic_hS p hp s hs) L x hx

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, S.one_mem, fun v hv => by simp at hv⟩`. Consider the case `@insert a s ha ih`. Take `⟨u, hu, hus⟩` from `ih (fun v hv => hf v (Finset.mem_insert_of_mem hv))`. Take `⟨w, hw, hwa⟩` from `hf a (Finset.mem_insert_self a s)`.

Use `⟨u * w, S.mul_mem hu hw, fun v hv => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hv with rfl | hv` into its components or cases. Rewrite using `[map_mul, mul_assoc]`. Conclude with `genusBasic_mem_one_mul _ hwa u`. Rewrite using `[map_mul, mul_comm (algebraMap R K u), mul_assoc]`.

Conclude with `genusBasic_mem_one_mul _ (hus v hv) w`.
-/
theorem genusBasic_common (S : Submonoid R) (s : Finset V) (f : V → K)
    (hf : ∀ v ∈ s, ∃ u ∈ S, algebraMap R K u * f v ∈ (1 : Submodule R K)) :
    ∃ u ∈ S, ∀ v ∈ s, algebraMap R K u * f v ∈ (1 : Submodule R K) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, S.one_mem, fun v hv => by simp at hv⟩
  | @insert a s ha ih =>
    obtain ⟨u, hu, hus⟩ := ih (fun v hv => hf v (Finset.mem_insert_of_mem hv))
    obtain ⟨w, hw, hwa⟩ := hf a (Finset.mem_insert_self a s)
    refine ⟨u * w, S.mul_mem hu hw, fun v hv => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [map_mul, mul_assoc]
      exact genusBasic_mem_one_mul _ hwa u
    · rw [map_mul, mul_comm (algebraMap R K u), mul_assoc]
      exact genusBasic_mem_one_mul _ (hus v hv) w

/- English proof (translation)
Take `⟨gens, rfl⟩` from `hL`. Establish `hgen : ∀ v ∈ gens, ∃ u ∈ hcompl (K` using `K) p, algebraMap R K u * h v z ∈ (1 : Submodule R K) := by`. Introduce `v hv`. Take `⟨s, hs, hsv⟩` from `locBasic_mem_locS.1 (hz v (Submodule.subset_span hv))`. Conclude with `⟨s, hs, by rw [← Algebra.smul_def]; exact hsv⟩`.

Take `⟨u, hu, hall⟩` from `genusBasic_common (hcompl (K := K) p) gens (fun v => h v z) hgen`. Use `locBasic_mem_locS.2 ⟨u, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[dualBasic_mem_dual]`. Introduce `y hy`. Rewrite using `[genusBasic_hsmul_right]`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact hall x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, LinearMap.add_apply, mul_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[genusBasic_hsmul_left hinj hstar, mul_left_comm]`. Conclude with `genusBasic_mem_one_mul _ hx _`.
-/
theorem genusBasic_loc_dual (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (hL : L.FG) (z : V)
    (hz : ∀ v ∈ L, h v z ∈ loc (K := K) p (1 : Submodule R K)) :
    z ∈ loc (K := K) p (dual h L) := by
  obtain ⟨gens, rfl⟩ := hL
  have hgen : ∀ v ∈ gens, ∃ u ∈ hcompl (K := K) p,
      algebraMap R K u * h v z ∈ (1 : Submodule R K) := by
    intro v hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 (hz v (Submodule.subset_span hv))
    exact ⟨s, hs, by rw [← Algebra.smul_def]; exact hsv⟩
  obtain ⟨u, hu, hall⟩ := genusBasic_common (hcompl (K := K) p) gens (fun v => h v z) hgen
  refine locBasic_mem_locS.2 ⟨u, hu, ?_⟩
  rw [dualBasic_mem_dual]
  intro y hy
  rw [genusBasic_hsmul_right]
  induction hy using Submodule.span_induction with
  | mem x hx => exact hall x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply, mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [genusBasic_hsmul_left hinj hstar, mul_left_comm]
    exact genusBasic_mem_one_mul _ hx _

/- English proof (translation)
Introduce `p hp`. Take `⟨g, hg, hgL⟩` from `hLM p hp`. Conclude with `⟨g⁻¹, (isom h).inv_mem hg, by rw [← hgL, genusBasic_gmap_inv]⟩`.
-/
theorem genusBasic_symm (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V)
    (hLM : SameGenus h L M) : SameGenus h M L := by
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  exact ⟨g⁻¹, (isom h).inv_mem hg, by rw [← hgL, genusBasic_gmap_inv]⟩

/- English proof (translation)
Introduce `x hx y hy`. Apply `genusBasic_lg (K := K) (1 : Submodule R K) (h x y)` to reduce the goal to its premises. Introduce `p hp`. Take `⟨g, hg, hgL⟩` from `hLM p hp`. Establish `hx' : x ∈ gmap g (loc (K` using `K) p L) := by`.

Rewrite using `[hgL]`. Conclude with `locBasic_le_locS _ _ hx`. Establish `hy' : y ∈ gmap g (loc (K` using `K) p L) := by`. Rewrite using `[hgL]`. Conclude with `locBasic_le_locS _ _ hy`.

Rewrite `hx'`, `hy'` using `[isomAct_mem_gmap]`. Take `⟨s, hs, hsx⟩` from `locBasic_mem_locS.1 hx'`. Take `⟨t, ht, hty⟩` from `locBasic_mem_locS.1 hy'`. Establish `hiso : h (g.symm x) (g.symm y) = h x y`. Establish `e` using `hg (g.symm x) (g.symm y)`.

Simplify using `using e.symm`. Use `locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s * t, Submonoid.mul_mem _ (genusBasic_sigma_mem hinj hstar p s hs) ht, ?_⟩` and prove the remaining obligations. Establish `h1` using `hL _ hsx _ hty`. Rewrite `h1` using `[genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso]`. Rewrite using `[Algebra.smul_def, map_mul]`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem genusBasic_int (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLM : SameGenus h L M)
    (hL : IsIntegralLat h L) : IsIntegralLat h M := by
  intro x hx y hy
  apply genusBasic_lg (K := K) (1 : Submodule R K) (h x y)
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  have hx' : x ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hx
  have hy' : y ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hy
  rw [isomAct_mem_gmap] at hx' hy'
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.1 hx'
  obtain ⟨t, ht, hty⟩ := locBasic_mem_locS.1 hy'
  have hiso : h (g.symm x) (g.symm y) = h x y := by
    have e := hg (g.symm x) (g.symm y)
    simpa using e.symm
  refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s * t,
    Submonoid.mul_mem _ (genusBasic_sigma_mem hinj hstar p s hs) ht, ?_⟩
  have h1 := hL _ hsx _ hty
  rw [genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso] at h1
  rw [Algebra.smul_def, map_mul]
  convert h1 using 1
  ring

/- English proof (translation)
Introduce `z hz`. Rewrite `hz` using `[dualBasic_mem_dual]`. Apply `genusBasic_lg (K := K) M z` to reduce the goal to its premises. Introduce `p hp`. Take `⟨g, hg, hgL⟩` from `hLM p hp`.

Rewrite using `[← hgL, isomAct_mem_gmap]`. Establish `hmem : g.symm z ∈ loc (K` using `K) p (dual h L) := by`. Apply `genusBasic_loc_dual hinj hstar h p L hLfg` to reduce the goal to its premises. Introduce `v hv`. Establish `hgv : g v ∈ loc (K` using `K) p M := by`.

Rewrite using `[← hgL, isomAct_mem_gmap, LinearEquiv.symm_apply_apply]`. Conclude with `locBasic_le_locS _ _ hv`. Take `⟨s, hs, hsv⟩` from `locBasic_mem_locS.1 hgv`. Establish `h1` using `hz _ hsv`. Rewrite `h1` using `[genusBasic_hsmul_left hinj hstar]`.

Establish `hiso : h (g v) z = h v (g.symm z)`. Establish `e` using `hg v (g.symm z)`. Simplify using `using e`. Use `locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s, genusBasic_sigma_mem hinj hstar p s hs, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, ← hiso]`.

Conclude with `h1`. Rewrite `hmem` using `[show dual h L = L from hL]`. Then use the resulting hypothesis.
-/
theorem genusBasic_dual_le (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLfg : L.FG) (hLM : SameGenus h L M)
    (hL : IsUnimodular h L) : dual h M ≤ M := by
  intro z hz
  rw [dualBasic_mem_dual] at hz
  apply genusBasic_lg (K := K) M z
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  rw [← hgL, isomAct_mem_gmap]
  have hmem : g.symm z ∈ loc (K := K) p (dual h L) := by
    apply genusBasic_loc_dual hinj hstar h p L hLfg
    intro v hv
    have hgv : g v ∈ loc (K := K) p M := by
      rw [← hgL, isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
      exact locBasic_le_locS _ _ hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 hgv
    have h1 := hz _ hsv
    rw [genusBasic_hsmul_left hinj hstar] at h1
    have hiso : h (g v) z = h v (g.symm z) := by
      have e := hg v (g.symm z)
      simpa using e
    refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s,
      genusBasic_sigma_mem hinj hstar p s hs, ?_⟩
    rw [Algebra.smul_def, ← hiso]
    exact h1
  rwa [show dual h L = L from hL] at hmem

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `R K V _ _ _ _ _ _ _ _ _ _ h _ hstar`. Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `hint_of : ∀ L : Submodule R V, IsUnimodular h L → IsIntegralLat h L`. Introduce `L hL x hx y hy`. Establish `hy' : y ∈ dual h L`.

Rewrite using `[show dual h L = L from hL]`. Conclude with `hy`. Conclude with `(dualBasic_mem_dual h L y).1 hy' x hx`. Establish `hle_dual : ∀ L : Submodule R V, IsIntegralLat h L → L ≤ dual h L`. Introduce `L hL y hy`.

Conclude with `(dualBasic_mem_dual h L y).2 fun x hx => hL x hx y hy`. Use `⟨⟨fun L p hp => ⟨1, (isom h).one_mem, by rw [genusBasic_gmap_one]⟩, fun {L M} hLM => genusBasic_symm h L M hLM, fun {L M N} h1 h2 p hp => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Take `⟨g₁, hg₁, e₁⟩` from `h1 p hp`. Take `⟨g₂, hg₂, e₂⟩` from `h2 p hp`. Conclude with `⟨g₂ * g₁, (isom h).mul_mem hg₂ hg₁, by rw [genusBasic_gmap_mul, e₁, e₂]⟩`.

Introduce `L g hg p hp`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [loc, isomAct_mem_gmap, locBasic_mem_locS, isomAct_smul]`. Introduce `L M hL hM hLM`.

Establish `hML` using `genusBasic_symm h L M hLM`. Use `⟨⟨fun hU => ?_, fun hU => ?_⟩, ⟨genusBasic_int hinj hstar h L M hLM, genusBasic_int hinj hstar h M L hML⟩⟩` and prove the remaining obligations. Conclude with `le_antisymm (genusBasic_dual_le hinj hstar h L M hL hLM hU) (hle_dual M (genusBasic_int hinj hstar h L M hLM (hint_of L hU)))`. Conclude with `le_antisymm (genusBasic_dual_le hinj hstar h M L hM hML hU) (hle_dual L (genusBasic_int hinj hstar h M L hML (hint_of M hU)))`.
-/
theorem genusBasic : GenusBasic := by
  intro R K V _ _ _ _ _ _ _ _ _ _ h _ hstar
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hint_of : ∀ L : Submodule R V, IsUnimodular h L → IsIntegralLat h L := by
    intro L hL x hx y hy
    have hy' : y ∈ dual h L := by
      rw [show dual h L = L from hL]
      exact hy
    exact (dualBasic_mem_dual h L y).1 hy' x hx
  have hle_dual : ∀ L : Submodule R V, IsIntegralLat h L → L ≤ dual h L := by
    intro L hL y hy
    exact (dualBasic_mem_dual h L y).2 fun x hx => hL x hx y hy
  refine ⟨⟨fun L p hp => ⟨1, (isom h).one_mem, by rw [genusBasic_gmap_one]⟩,
    fun {L M} hLM => genusBasic_symm h L M hLM, fun {L M N} h1 h2 p hp => ?_⟩, ?_, ?_⟩
  · obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
    obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
    exact ⟨g₂ * g₁, (isom h).mul_mem hg₂ hg₁, by rw [genusBasic_gmap_mul, e₁, e₂]⟩
  · intro L g hg p hp
    refine ⟨g, hg, ?_⟩
    ext x
    simp only [loc, isomAct_mem_gmap, locBasic_mem_locS, isomAct_smul]
  · intro L M hL hM hLM
    have hML := genusBasic_symm h L M hLM
    refine ⟨⟨fun hU => ?_, fun hU => ?_⟩,
      ⟨genusBasic_int hinj hstar h L M hLM, genusBasic_int hinj hstar h M L hML⟩⟩
    · exact le_antisymm (genusBasic_dual_le hinj hstar h L M hL hLM hU)
        (hle_dual M (genusBasic_int hinj hstar h L M hLM (hint_of L hU)))
    · exact le_antisymm (genusBasic_dual_le hinj hstar h M L hM hML hU)
        (hle_dual L (genusBasic_int hinj hstar h M L hML (hint_of M hU)))

end Formalism.HermitianLatticesTheory
