import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

/- English proof (translation)
Set `m` to `T.toHomeomorph.toMeasurableEquiv`. Use `haveI : (μ.map m).IsAddHaarMeasure := T.isAddHaarMeasure_map μ`. Set `e : N ≃ N` to `{ toFun := fun n => ⟨T.symm n, hT' _ n.2⟩ invFun := fun n => ⟨T n, hT _ n.2⟩ left_inv := fun n => Subtype.ext (T.apply_symm_apply _) right_inv := fun n => Subtype.ext (T.symm_apply_apply _) }`. Establish `hD : IsAddFundamentalDomain N (m '' 𝓕) (μ.map m)` using `h𝓕.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun n x => by`. Express the relevant statement in the definitionally equal form `T (T.symm n + x) = n + T x`.

Rewrite using `[map_add, T.apply_symm_apply]`. Establish `hD2 : IsAddFundamentalDomain N 𝓕 (μ.map m)` using `h𝓕.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)`. Establish `hinv : ∀ (n : N) (x : X), f (n +ᵥ x) = f x` using `fun n x => hf n n.2 x`. Take `⟨c, hc⟩ : ∃ c : NNReal, μ.map m = c • μ` from `⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map m) μ⟩`. Establish `hm : (μ.map m) (m '' 𝓕) = 1`.

Rewrite using `[m.map_apply, m.preimage_image, h1]`. Establish `hc1 : c = 1`. Establish `h3` using `hD.measure_eq hD2`. Rewrite `h3` using `[hm, hc, Measure.smul_apply, h1]`. Establish `h4 : (c : ENNReal) = 1` using `by simpa [ENNReal.smul_def] using h3.symm`.

Conclude with `h4` after adjusting the coercions. Establish `step` using `m.measurableEmbedding.setIntegral_map (μ := μ) f (m '' 𝓕)`. Rewrite `step` using `[m.preimage_image]`. Express the relevant statement in the definitionally equal form `∫ x in 𝓕, f (m x) ∂μ = _`. Rewrite using `[← step, hD.setIntegral_eq hD2 hinv, hc, hc1, one_smul]`.
-/
theorem setIntegral_comp_contAddEquiv {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    (N : AddSubgroup X) [Countable N] {𝓕 : Set X} (h𝓕 : IsAddFundamentalDomain N 𝓕 μ) (h1 : μ 𝓕 = 1)
    (T : X ≃ₜ+ X) (hT : ∀ n ∈ N, T n ∈ N) (hT' : ∀ n ∈ N, T.symm n ∈ N)
    (f : X → ℂ) (hf : ∀ n ∈ N, ∀ x, f (n + x) = f x) :
    ∫ x in 𝓕, f (T x) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  let m := T.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map m).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  let e : N ≃ N :=
    { toFun := fun n => ⟨T.symm n, hT' _ n.2⟩
      invFun := fun n => ⟨T n, hT _ n.2⟩
      left_inv := fun n => Subtype.ext (T.apply_symm_apply _)
      right_inv := fun n => Subtype.ext (T.symm_apply_apply _) }
  have hD : IsAddFundamentalDomain N (m '' 𝓕) (μ.map m) :=
    h𝓕.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e
      fun n x => by
        change T (T.symm n + x) = n + T x
        rw [map_add, T.apply_symm_apply]
  have hD2 : IsAddFundamentalDomain N 𝓕 (μ.map m) :=
    h𝓕.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hinv : ∀ (n : N) (x : X), f (n +ᵥ x) = f x := fun n x => hf n n.2 x
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map m = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map m) μ⟩
  have hm : (μ.map m) (m '' 𝓕) = 1 := by
    rw [m.map_apply, m.preimage_image, h1]
  have hc1 : c = 1 := by
    have h3 := hD.measure_eq hD2
    rw [hm, hc, Measure.smul_apply, h1] at h3
    have h4 : (c : ENNReal) = 1 := by simpa [ENNReal.smul_def] using h3.symm
    exact_mod_cast h4
  have step := m.measurableEmbedding.setIntegral_map (μ := μ) f (m '' 𝓕)
  rw [m.preimage_image] at step
  change ∫ x in 𝓕, f (m x) ∂μ = _
  rw [← step, hD.setIntegral_eq hD2 hinv, hc, hc1, one_smul]

section Shear

variable {R : Type} [CommRing R] {a r : ℕ}

def shear (D : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) : BlockIx a r → R :=
  fun p => (nilM x * D) p.1.1 p.1.2

/- English proof (translation)
Unfold `nilM`. Rewrite using `[Matrix.of_apply, dif_pos p.2]`.
-/
theorem nilM_apply_ix (x : BlockIx a r → R) (p : BlockIx a r) : nilM x p.1.1 p.1.2 = x p := by
  unfold nilM
  rw [Matrix.of_apply, dif_pos p.2]

/- English proof (translation)
Introduce `x y h`. Use function extensionality and compare the values at `p`. Establish `h'` using `congrFun (congrFun h p.1.1) p.1.2`. Simplify using `only at h'`. Rewrite `h'` using `[nilM_apply_ix, nilM_apply_ix]`. Then use the resulting hypothesis.
-/
theorem nilM_injective : Function.Injective (fun x : BlockIx a r → R => nilM x) := by
  intro x y h
  funext p
  have h' := congrFun (congrFun h p.1.1) p.1.2
  simp only at h'
  rwa [nilM_apply_ix, nilM_apply_ix] at h'

/- English proof (translation)
Apply the tactic sequence `ext i j; simp only [nilM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp`.
-/
theorem nilM_add (x y : BlockIx a r → R) : nilM (x + y) = nilM x + nilM y := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [shear, nilM_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]`.
-/
theorem shear_add (D : Matrix (Fin a) (Fin a) R) (x y : BlockIx a r → R) :
    shear D (x + y) = shear D x + shear D y := by
  funext p
  simp only [shear, nilM_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : (i : ℕ) < r ∧ r ≤ (j : ℕ)`. Use `conv_lhs => rw [nilM, Matrix.of_apply, dif_pos h]`. Both sides reduce to the same expression. Establish `h0 : nilM (shear D x) i j = 0`.

Unfold `nilM`. Rewrite using `[Matrix.of_apply, dif_neg h]`. Rewrite using `[h0, Matrix.mul_apply]`. Use `(Finset.sum_eq_zero fun k _ => ?_).symm` and prove the remaining obligations. Distinguish the cases in `hk : (i : ℕ) < r ∧ r ≤ (k : ℕ)`.

Rewrite using `[hD k j hk.2 (by omega), mul_zero]`. Establish `h1 : nilM x i k = 0`. Unfold `nilM`. Rewrite using `[Matrix.of_apply, dif_neg hk]`. Rewrite using `[h1, zero_mul]`.
-/
theorem nilM_shear (D : Matrix (Fin a) (Fin a) R) (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D i j = 0)
    (x : BlockIx a r → R) : nilM (shear D x) = nilM x * D := by
  ext i j
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · conv_lhs => rw [nilM, Matrix.of_apply, dif_pos h]
    rfl
  · have h0 : nilM (shear D x) i j = 0 := by
      unfold nilM
      rw [Matrix.of_apply, dif_neg h]
    rw [h0, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    by_cases hk : (i : ℕ) < r ∧ r ≤ (k : ℕ)
    · rw [hD k j hk.2 (by omega), mul_zero]
    · have h1 : nilM x i k = 0 := by
        unfold nilM
        rw [Matrix.of_apply, dif_neg hk]
      rw [h1, zero_mul]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hi : (i : ℕ) < r`. Rewrite using `[show (∑ k, D i k * nilM x k j) = ∑ k, (1 : Matrix (Fin a) (Fin a) R) i k * nilM x k j from Finset.sum_congr rfl fun k _ => by rw [hD1 i k hi]]`. Rewrite using `[← Matrix.mul_apply, Matrix.one_mul]`.

Establish `h0 : nilM x i j = 0`. Unfold `nilM`. Rewrite using `[Matrix.of_apply, dif_neg (fun h => hi h.1)]`. Rewrite using `[h0]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : (k : ℕ) < r ∧ r ≤ (j : ℕ)`. Rewrite using `[hD i k (by omega) hk.1, zero_mul]`. Establish `h1 : nilM x k j = 0`. Unfold `nilM`. Rewrite using `[Matrix.of_apply, dif_neg hk]`.

Rewrite using `[h1, mul_zero]`.
-/
theorem mul_nilM (D : Matrix (Fin a) (Fin a) R)
    (hD1 : ∀ i j : Fin a, (i : ℕ) < r → D i j = (1 : Matrix (Fin a) (Fin a) R) i j)
    (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D i j = 0) (x : BlockIx a r → R) : D * nilM x = nilM x := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) < r
  · rw [show (∑ k, D i k * nilM x k j) = ∑ k, (1 : Matrix (Fin a) (Fin a) R) i k * nilM x k j from
      Finset.sum_congr rfl fun k _ => by rw [hD1 i k hi]]
    rw [← Matrix.mul_apply, Matrix.one_mul]
  · have h0 : nilM x i j = 0 := by
      unfold nilM
      rw [Matrix.of_apply, dif_neg (fun h => hi h.1)]
    rw [h0]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < r ∧ r ≤ (j : ℕ)
    · rw [hD i k (by omega) hk.1, zero_mul]
    · have h1 : nilM x k j = 0 := by
        unfold nilM
        rw [Matrix.of_apply, dif_neg hk]
      rw [h1, mul_zero]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(1 + nilM x) * (D : Matrix (Fin a) (Fin a) R) = (D : Matrix (Fin a) (Fin a) R) * (1 + nilM (shear (D : Matrix (Fin a) (Fin a) R) x))`. Rewrite using `[nilM_shear _ hD, add_mul, mul_add, one_mul, mul_one, ← mul_assoc, mul_nilM _ hD1 hD]`.
-/
theorem unip_mul_eq (D : GL (Fin a) R)
    (hD1 : ∀ i j : Fin a, (i : ℕ) < r → (D : Matrix (Fin a) (Fin a) R) i j = (1 : Matrix (Fin a) (Fin a) R) i j)
    (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → (D : Matrix (Fin a) (Fin a) R) i j = 0)
    (x : BlockIx a r → R) : unip x * D = D * unip (shear (D : Matrix (Fin a) (Fin a) R) x) := by
  apply Units.ext
  change (1 + nilM x) * (D : Matrix (Fin a) (Fin a) R) =
    (D : Matrix (Fin a) (Fin a) R) * (1 + nilM (shear (D : Matrix (Fin a) (Fin a) R) x))
  rw [nilM_shear _ hD, add_mul, mul_add, one_mul, mul_one, ← mul_assoc, mul_nilM _ hD1 hD]

/- English proof (translation)
Apply `nilM_injective` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[nilM_shear _ hD', nilM_shear _ hD, Matrix.mul_assoc, h, Matrix.mul_one]`.
-/
theorem shear_shear (D D' : Matrix (Fin a) (Fin a) R)
    (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D i j = 0)
    (hD' : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D' i j = 0) (h : D * D' = 1) (x : BlockIx a r → R) :
    shear D' (shear D x) = x := by
  apply nilM_injective
  simp only
  rw [nilM_shear _ hD', nilM_shear _ hD, Matrix.mul_assoc, h, Matrix.mul_one]

/- English proof (translation)
Establish `hN : Continuous fun x : BlockIx a r → R => nilM x`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Unfold `nilM`. Simplify using `only [Matrix.of_apply]`. Use `split_ifs`.

Conclude with `continuous_apply _`. Conclude with `continuous_const`. Establish `hM : Continuous fun x : BlockIx a r → R => nilM x * D` using `hN.matrix_mul continuous_const`. Conclude with `continuous_pi fun p => (hM.matrix_elem p.1.1 p.1.2)`.
-/
theorem continuous_shear [TopologicalSpace R] [IsTopologicalRing R] (D : Matrix (Fin a) (Fin a) R) :
    Continuous (shear (r := r) D) := by
  have hN : Continuous fun x : BlockIx a r → R => nilM x := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    unfold nilM
    simp only [Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  have hM : Continuous fun x : BlockIx a r → R => nilM x * D := hN.matrix_mul continuous_const
  exact continuous_pi fun p => (hM.matrix_elem p.1.1 p.1.2)

/- English proof (translation)
Apply the tactic sequence `ext i j; simp only [nilM, Matrix.of_apply, Matrix.map_apply]; split_ifs <;> simp`.
-/
theorem nilM_map {S : Type} [CommRing S] (f : R →+* S) (x : BlockIx a r → R) :
    nilM (fun p => f (x p)) = (nilM x).map f := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.map_apply]; split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [shear]`. Rewrite using `[nilM_map, ← Matrix.map_mul]`. Both sides reduce to the same expression.
-/
theorem shear_map {S : Type} [CommRing S] (f : R →+* S) (D : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) :
    shear (D.map f) (fun p => f (x p)) = fun p => f (shear D x p) := by
  funext p
  simp only [shear]
  rw [nilM_map, ← Matrix.map_mul]
  rfl

/- English proof (translation)
Take `⟨i, rfl⟩` from `(blkEquiv hr).surjective i`. Take `⟨j, rfl⟩` from `(blkEquiv hr).surjective j`. Rewrite using `[blkGL_apply]`. Establish `e1 : (1 : Matrix (Fin a) (Fin a) R) (blkEquiv hr i) (blkEquiv hr j) = (1 : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (a - r)) R) i j`. Simplify using `[Matrix.one_apply, (blkEquiv hr).injective.eq_iff]`.

Rewrite using `[e1]`. Break down `i with i | i` into its components or cases. Apply the tactic sequence `rcases j with j | j <;> simp [Matrix.one_apply]`. It suffices to derive a contradiction. Rewrite `hi` using `[blkEquiv_inr]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem blkGL_one_top (hr : r ≤ a) (l : GL (Fin (a - r)) R) (i j : Fin a) (hi : (i : ℕ) < r) :
    (blkGL hr (1, l) : Matrix (Fin a) (Fin a) R) i j = (1 : Matrix (Fin a) (Fin a) R) i j := by
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  rw [blkGL_apply]
  have e1 : (1 : Matrix (Fin a) (Fin a) R) (blkEquiv hr i) (blkEquiv hr j) =
      (1 : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (a - r)) R) i j := by
    simp [Matrix.one_apply, (blkEquiv hr).injective.eq_iff]
  rw [e1]
  rcases i with i | i
  · rcases j with j | j <;> simp [Matrix.one_apply]
  · exfalso
    rw [blkEquiv_inr] at hi
    omega

/- English proof (translation)
Break down `blkGL_block hr (1, l) i j with h | h` into its components or cases. Conclude with `absurd (h.2 hj) (by omega)`. Conclude with `h`.
-/
theorem blkGL_one_low (hr : r ≤ a) (l : GL (Fin (a - r)) R) (i j : Fin a) (hi : r ≤ (i : ℕ)) (hj : (j : ℕ) < r) :
    (blkGL hr (1, l) : Matrix (Fin a) (Fin a) R) i j = 0 := by
  rcases blkGL_block hr (1, l) i j with h | h
  · exact absurd (h.2 hj) (by omega)
  · exact h

end Shear

/- English proof (translation)
Introduce `E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 h1 φ _ hφ m₁ t κ γ g`. Use `haveI := hμ`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E`. Use `haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm`.

Use `haveI : Countable (ratN E a r) := by`. Establish `: ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r))` using `AddMonoidHom.coe_range _`. Express the relevant statement in the definitionally equal form `Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))`. Rewrite using `[this]`. Conclude with `(Set.countable_range _).to_subtype`.

Set `G : GL (Fin a) E` to `blkGL hr (1, γ)`. Establish `hDG : ratGL E a G = blkGL hr (1, ratGL E (a - r) γ)` using `(map_blkGL hr (algebraMap E (Ad E)) (1, γ)).trans (by rw [map_one]; rfl)`. Establish `hDG' : (ratGL E a G)⁻¹ = blkGL hr (1, (ratGL E (a - r) γ)⁻¹)`. Rewrite using `[hDG, ← map_inv, Prod.inv_mk, inv_one]`. Set `M : Matrix (Fin a) (Fin a) (Ad E)` to `(ratGL E a G : Matrix (Fin a) (Fin a) (Ad E))`.

Set `M' : Matrix (Fin a) (Fin a) (Ad E)` to `((ratGL E a G)⁻¹ : GA E a)`. Establish `hM1 : ∀ i j : Fin a, (i : ℕ) < r → M i j = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j` using `fun i j hi => by`. Express the relevant statement in the definitionally equal form `((ratGL E a G : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _`. Rewrite using `[hDG]`. Conclude with `blkGL_one_top hr _ i j hi`.

Establish `hM2 : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → M i j = 0` using `fun i j hi hj => by`. Express the relevant statement in the definitionally equal form `((ratGL E a G : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _`. Rewrite using `[hDG]`. Conclude with `blkGL_one_low hr _ i j hi hj`. Establish `hM2' : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → M' i j = 0` using `fun i j hi hj => by`.

Express the relevant statement in the definitionally equal form `(((ratGL E a G)⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _`. Rewrite using `[hDG']`. Conclude with `blkGL_one_low hr _ i j hi hj`. Establish `hMM' : M * M' = 1` using `Units.mul_inv _`. Establish `hM'M : M' * M = 1` using `Units.inv_mul _`.

Set `T : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E)` to `{ toFun := shear M invFun := shear M' left_inv := fun x => shear_shear M M' hM2 hM2' hMM' x right_inv := fun x => shear_shear M' M hM2' hM2 hM'M x map_add' := shear_add M continuous_toFun := continuous_shear M continuous_invFun := continuous_shear M' }`. Establish `hT : ∀ n ∈ ratN E a r, T n ∈ ratN E a r`. Introduce and unpack `_ ⟨e, rfl⟩`. Conclude with `⟨shear (G : Matrix (Fin a) (Fin a) E) e, (shear_map (algebraMap E (Ad E)) _ e).symm⟩`. Establish `hT' : ∀ n ∈ ratN E a r, T.symm n ∈ ratN E a r`.

Introduce and unpack `_ ⟨e, rfl⟩`. Conclude with `⟨shear ((G⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) e, (shear_map (algebraMap E (Ad E)) _ e).symm⟩`. Set `B : GA E a` to `blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)`. Set `f : (BlockIx a r → Ad E) → ℂ` to `fun y => φ (unip y * B)`. Establish `hf : ∀ n ∈ ratN E a r, ∀ x, f (n + x) = f x`.

Introduce and unpack `_ ⟨e, rfl⟩ x`. Express the relevant statement in the definitionally equal form `φ (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * B) = φ (unip x * B)`. Rewrite using `[unip_add, unip_algebraMap, mul_assoc, hφ]`. Establish `key : ∀ x, φ (unip x * (blkGL hr (m₁, ratGL E (a - r) γ * g) * finGL E a t * infGL E a (Unitary.toUnits κ))) = f (T x)` using `fun x => by`. Rewrite using `[show (m₁, ratGL E (a - r) γ * g) = ((1 : GA E r), ratGL E (a - r) γ) * (m₁, g) by simp, map_mul, ← hDG]`.

Express the relevant statement in the definitionally equal form `_ = φ (unip (shear M x) * (blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)))`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (unip x) (ratGL E a G), unip_mul_eq (ratGL E a G) hM1 hM2, mul_assoc, hφ]`. Unfold `slice`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem slice_ratGL_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : GA E a → ℂ, Continuous φ → (∀ γ g, φ (ratGL E a γ * g) = φ g) →
    ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (γ : GL (Fin (a - r)) E) (g : GA E (a - r)),
    GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ (ratGL E (a - r) γ * g) = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ g := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 h1 φ _ hφ m₁ t κ γ g
  haveI := hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype

  let G : GL (Fin a) E := blkGL hr (1, γ)
  have hDG : ratGL E a G = blkGL hr (1, ratGL E (a - r) γ) :=
    (map_blkGL hr (algebraMap E (Ad E)) (1, γ)).trans (by rw [map_one]; rfl)
  have hDG' : (ratGL E a G)⁻¹ = blkGL hr (1, (ratGL E (a - r) γ)⁻¹) := by
    rw [hDG, ← map_inv, Prod.inv_mk, inv_one]
  let M : Matrix (Fin a) (Fin a) (Ad E) := (ratGL E a G : Matrix (Fin a) (Fin a) (Ad E))
  let M' : Matrix (Fin a) (Fin a) (Ad E) := ((ratGL E a G)⁻¹ : GA E a)
  have hM1 : ∀ i j : Fin a, (i : ℕ) < r → M i j = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j := fun i j hi => by
    change ((ratGL E a G : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _
    rw [hDG]; exact blkGL_one_top hr _ i j hi
  have hM2 : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → M i j = 0 := fun i j hi hj => by
    change ((ratGL E a G : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _
    rw [hDG]; exact blkGL_one_low hr _ i j hi hj
  have hM2' : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → M' i j = 0 := fun i j hi hj => by
    change (((ratGL E a G)⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _
    rw [hDG']; exact blkGL_one_low hr _ i j hi hj
  have hMM' : M * M' = 1 := Units.mul_inv _
  have hM'M : M' * M = 1 := Units.inv_mul _
  let T : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := shear M
      invFun := shear M'
      left_inv := fun x => shear_shear M M' hM2 hM2' hMM' x
      right_inv := fun x => shear_shear M' M hM2' hM2 hM'M x
      map_add' := shear_add M
      continuous_toFun := continuous_shear M
      continuous_invFun := continuous_shear M' }
  have hT : ∀ n ∈ ratN E a r, T n ∈ ratN E a r := by
    rintro _ ⟨e, rfl⟩
    exact ⟨shear (G : Matrix (Fin a) (Fin a) E) e, (shear_map (algebraMap E (Ad E)) _ e).symm⟩
  have hT' : ∀ n ∈ ratN E a r, T.symm n ∈ ratN E a r := by
    rintro _ ⟨e, rfl⟩
    exact ⟨shear ((G⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) e, (shear_map (algebraMap E (Ad E)) _ e).symm⟩

  let B : GA E a := blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)
  let f : (BlockIx a r → Ad E) → ℂ := fun y => φ (unip y * B)
  have hf : ∀ n ∈ ratN E a r, ∀ x, f (n + x) = f x := by
    rintro _ ⟨e, rfl⟩ x
    change φ (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * B) = φ (unip x * B)
    rw [unip_add, unip_algebraMap, mul_assoc, hφ]
  have key : ∀ x, φ (unip x * (blkGL hr (m₁, ratGL E (a - r) γ * g) * finGL E a t * infGL E a (Unitary.toUnits κ))) =
      f (T x) := fun x => by
    rw [show (m₁, ratGL E (a - r) γ * g) = ((1 : GA E r), ratGL E (a - r) γ) * (m₁, g) by simp, map_mul, ← hDG]
    change _ = φ (unip (shear M x) * (blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)))
    simp only [mul_assoc]
    rw [← mul_assoc (unip x) (ratGL E a G), unip_mul_eq (ratGL E a G) hM1 hM2, mul_assoc, hφ]
  unfold slice
  calc ∫ x in 𝓕, φ (unip x * (blkGL hr (m₁, ratGL E (a - r) γ * g) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ
      = ∫ x in 𝓕, f (T x) ∂μ := by congr 1; funext x; exact key x
    _ = ∫ x in 𝓕, f x ∂μ := setIntegral_comp_contAddEquiv μ (ratN E a r) h𝓕 h1 T hT hT' f hf

end GlobalTheory.SliceTwo

end
