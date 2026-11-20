import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralPreimageAddImageEqLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianDualSubsetOfIntegralGramStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormIntegralPreimageLatticeStatement
open Matrix

/- English proof (translation)
Introduce `L _ _ ϖ σ q n n' JS JT hU _hq hJS hJT hS hT x hx`. Establish `hσσ : ∀ z, σ (σ z) = z` using `hU.1`. Establish `hσv : ∀ z, Valued.v (σ z) = Valued.v z` using `hU.2.1`. Establish `hσO : ∀ z ∈ Formalism.UG.intL L, σ z ∈ Formalism.UG.intL L`. Introduce `z hz`.

Express the relevant statement in the definitionally equal form `Valued.v (σ z) ≤ 1`. Rewrite using `[hσv]`. Conclude with `hz`. Establish `iMV : ∀ {k l : ℕ} (M : Matrix (Fin k) (Fin l) L) (t : Fin l → L), (∀ i j, M i j ∈ Formalism.UG.intL L) → (∀ j, t j ∈ Formalism.UG.intL L) → ∀ i, (M *ᵥ t) i ∈ Formalism.UG.intL L`. Introduce `k l M t hM ht i`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (ht j)`. Establish `iMM : ∀ {k l r : ℕ} (M : Matrix (Fin k) (Fin l) L) (M' : Matrix (Fin l) (Fin r) L), (∀ i j, M i j ∈ Formalism.UG.intL L) → (∀ i j, M' i j ∈ Formalism.UG.intL L) → ∀ i j, (M * M') i j ∈ Formalism.UG.intL L`. Introduce `k l r M M' hM hM' i j`. Simplify using `only [Matrix.mul_apply]`.

Conclude with `Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hM i m) (hM' m j)`. Establish `eJT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L`. Take `⟨g0, hg0⟩` from `hJT`. Introduce `i j`. Rewrite using `[← hg0]`.

Conclude with `((g0 : Matrix (Fin n') (Fin n') (Formalism.UG.intL L)) i j).2`. Use `set y := GlobalTheory.Hk3.HoweG.adj σ JS JT x with hy`. Establish `hxy : ∀ i j, (x * y) i j ∈ Formalism.UG.intL L`. Establish `: x * y = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) * (JT : Matrix (Fin n') (Fin n') L)`. Simplify using `only [hy, GlobalTheory.Hk3.HoweG.adj, Formalism.UG.cT, Matrix.mul_assoc]`.

Rewrite using `[this]`. Conclude with `iMM _ _ hx eJT`. Establish `T4` using `GlobalTheory.T.integral_preimage_add_image_eq_lattice`. Establish `T5` using `GlobalTheory.T.hermitianDual_subset_of_integral_gram`. Establish `FreeQuotientRank` using `GlobalTheory.T.hermitianForm_integral_preimage_lattice`.

Take `⟨a, ha⟩` from `T4 L n n' x y`. Establish `hcol : ∀ j, ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ (fun k => (a : Matrix (Fin n) (Fin n) L) k j) = u + y *ᵥ w`. Introduce `j`. Use `(ha _).mpr ⟨Pi.single j 1, fun i => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[Subring.one_mem]`. Simplify using `[h, Subring.zero_mem]`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec_single_one]`.

Establish `hN : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ u = (a : Matrix (Fin n) (Fin n) L) *ᵥ t`. Introduce `u hu hxu`. Conclude with `(ha u).mp ⟨u, 0, hu, hxu, fun _ => Subring.zero_mem _, by simp⟩`. Establish `hY : ∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) → ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ y *ᵥ w = (a : Matrix (Fin n) (Fin n) L) *ᵥ t`. Introduce `w hw`.

Conclude with `(ha _).mp ⟨0, w, fun _ => Subring.zero_mem _, by simp [Subring.zero_mem], hw, by simp⟩`. Establish `hformM : ∀ (M : Matrix (Fin n) (Fin n) L) (t : Fin n → L) (V : Matrix (Fin n) (Fin n) L) (j : Fin n), Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (M *ᵥ t) (fun l => V l j) = ∑ k, σ (t k) * (Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L) * V) k j`. Introduce `M t V j`. Simplify using `only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Eq.trans (Finset.sum_congr rfl fun x1 _ => Finset.sum_comm) ?_` and prove the remaining obligations. Use `symm`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Establish `hformC : ∀ (M : Matrix (Fin n) (Fin n) L) (i j : Fin n), (Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L) * M) i j = Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (fun k => M k i) (fun k => M k j)`.

Introduce `M i j`. Simplify using `only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `⟨a, ⟨?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`.

Take `⟨u, w, hu, hxu, hw, he⟩` from `hcol i`. Take `⟨u', w', hu', hxu', hw', he'⟩` from `hcol j`. Rewrite using `[hformC, he, he']`. Conclude with `FreeQuotientRank L σ n n' JS JT hσσ hσv hJS hJT hS hT x hx u u' w w' hu hxu hw hu' hxu' hw'`. Introduce `i j set V : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hV`.

Establish `hG : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * V = 1`. Rewrite using `[hV, Matrix.mul_assoc, ← Matrix.mul_assoc (JS : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.one_mul, ← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one]`. Establish `hAm : ∀ m : Fin n → L, (∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ m = (a : Matrix (Fin n) (Fin n) L) *ᵥ t) → Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) m (fun l => V l j) ∈ Formalism.UG.intL L`. Introduce and unpack `m ⟨t, ht, rfl⟩`. Rewrite using `[hformM, hG, Finset.sum_eq_single j]`.

Simplify using `only [Matrix.one_apply_eq, mul_one]`. Conclude with `hσO _ (ht j)`. Introduce `k _ hk`. Simplify using `[Matrix.one_apply_ne hk]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ j) h`. Take `⟨u, w, hu, hxu, hw, he⟩` from `T5 L σ n n' JS JT hσσ hσv hJS hJT hS hT x hx (fun l => V l j) (fun u hu hxu => hAm u (hN u hu hxu)) (fun w hw => hAm _ (hY w hw))`. Take `⟨t, ht, het⟩` from `(ha _).mp ⟨u, w, hu, hxu, hw, he⟩`. Establish `: (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * V) i j = t i`. Establish `h2 : ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (fun l => V l j) = t`.

Rewrite using `[het, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Rewrite using `[← h2]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`. Rewrite using `[Matrix.mul_assoc, ← hV, this]`. Conclude with `ht i`.

Introduce `y'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i j`. Take `⟨u, w, hu, hxu, hw, he⟩` from `hcol j`. Establish `: (y' * (a : Matrix (Fin n) (Fin n) L)) i j = (y' *ᵥ (fun k => (a : Matrix (Fin n) (Fin n) L) k j)) i`.

Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`. Rewrite using `[this, he, Matrix.mulVec_add]`. Conclude with `Subring.add_mem _ (h1 u hu hxu i) (h2 w hw i)`. Introduce `h`. Use `⟨fun u hu hxu i => ?_, fun w hw i => ?_⟩` and prove the remaining obligations.

Take `⟨t, ht, rfl⟩` from `hN u hu hxu`. Rewrite using `[Matrix.mulVec_mulVec]`. Conclude with `iMV _ _ h ht i`. Take `⟨t, ht, het⟩` from `hY w hw`. Rewrite using `[het, Matrix.mulVec_mulVec]`.

Conclude with `iMV _ _ h ht i`. Introduce `v hv`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩`. Take `⟨u, w, hu, hxu, hw, he⟩` from `(ha _).mpr ⟨t, ht, rfl⟩`.

Introduce `i`. Rewrite using `[he, Matrix.mulVec_add, Matrix.mulVec_mulVec]`. Conclude with `Subring.add_mem _ (hxu i) (iMV _ _ hxy hw i)`. Introduce `hxv`. Conclude with `hN v hv hxv`.

Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, v, ht, hv, rfl⟩`. Take `⟨u, w, hu, hxu, hw, he⟩` from `(ha _).mpr ⟨t, ht, rfl⟩`. Use `⟨u + v, w, fun i => Subring.add_mem _ (hu i) (hv i), hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[he]`. Normalize the expressions using the abelian group laws. Introduce and unpack `⟨v, w, hv, hw, rfl⟩`. Take `⟨t, ht, het⟩` from `hY w hw`. Conclude with `⟨t, v, ht, hv, by rw [het, add_comm]⟩`.
-/
theorem GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') := by
  intro L _ _ ϖ σ q n n' JS JT hU _hq hJS hJT hS hT x hx
  have hσσ : ∀ z, σ (σ z) = z := hU.1
  have hσv : ∀ z, Valued.v (σ z) = Valued.v z := hU.2.1
  have hσO : ∀ z ∈ Formalism.UG.intL L, σ z ∈ Formalism.UG.intL L := by
    intro z hz
    change Valued.v (σ z) ≤ 1
    rw [hσv]; exact hz
  have iMV : ∀ {k l : ℕ} (M : Matrix (Fin k) (Fin l) L) (t : Fin l → L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ j, t j ∈ Formalism.UG.intL L) → ∀ i, (M *ᵥ t) i ∈ Formalism.UG.intL L := by
    intro k l M t hM ht i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (ht j)
  have iMM : ∀ {k l r : ℕ} (M : Matrix (Fin k) (Fin l) L) (M' : Matrix (Fin l) (Fin r) L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ i j, M' i j ∈ Formalism.UG.intL L) → ∀ i j, (M * M') i j ∈ Formalism.UG.intL L := by
    intro k l r M M' hM hM' i j
    simp only [Matrix.mul_apply]
    exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hM i m) (hM' m j)
  have eJT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := by
    obtain ⟨g0, hg0⟩ := hJT
    intro i j; rw [← hg0]; exact ((g0 : Matrix (Fin n') (Fin n') (Formalism.UG.intL L)) i j).2
  set y := GlobalTheory.Hk3.HoweG.adj σ JS JT x with hy
  have hxy : ∀ i j, (x * y) i j ∈ Formalism.UG.intL L := by
    have : x * y = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *
        (JT : Matrix (Fin n') (Fin n') L) := by
      simp only [hy, GlobalTheory.Hk3.HoweG.adj, Formalism.UG.cT, Matrix.mul_assoc]
    rw [this]; exact iMM _ _ hx eJT
  have T4 := GlobalTheory.T.integral_preimage_add_image_eq_lattice
  have T5 := GlobalTheory.T.hermitianDual_subset_of_integral_gram
  have FreeQuotientRank := GlobalTheory.T.hermitianForm_integral_preimage_lattice
  obtain ⟨a, ha⟩ := T4 L n n' x y
  have hcol : ∀ j, ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
      (∀ i, w i ∈ Formalism.UG.intL L) ∧ (fun k => (a : Matrix (Fin n) (Fin n) L) k j) = u + y *ᵥ w := by
    intro j
    refine (ha _).mpr ⟨Pi.single j 1, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simp [Subring.one_mem]
      · simp [h, Subring.zero_mem]
    · funext k; simp [Matrix.mulVec_single_one]
  have hN : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ u = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
    intro u hu hxu
    exact (ha u).mp ⟨u, 0, hu, hxu, fun _ => Subring.zero_mem _, by simp⟩
  have hY : ∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) →
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ y *ᵥ w = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
    intro w hw
    exact (ha _).mp ⟨0, w, fun _ => Subring.zero_mem _, by simp [Subring.zero_mem], hw, by simp⟩
  have hformM : ∀ (M : Matrix (Fin n) (Fin n) L) (t : Fin n → L) (V : Matrix (Fin n) (Fin n) L) (j : Fin n),
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (M *ᵥ t) (fun l => V l j) =
        ∑ k, σ (t k) * (Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L) * V) k j := by
    intro M t V j
    simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun x1 _ => Finset.sum_comm) ?_
    symm; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hformC : ∀ (M : Matrix (Fin n) (Fin n) L) (i j : Fin n),
      (Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L) * M) i j =
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (fun k => M k i) (fun k => M k j) := by
    intro M i j
    simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  refine ⟨a, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨u, w, hu, hxu, hw, he⟩ := hcol i
    obtain ⟨u', w', hu', hxu', hw', he'⟩ := hcol j
    rw [hformC, he, he']
    exact FreeQuotientRank L σ n n' JS JT hσσ hσv hJS hJT hS hT x hx u u' w w' hu hxu hw hu' hxu' hw'
  · intro i j
    set V : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hV
    have hG : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * V = 1 := by
      rw [hV, Matrix.mul_assoc, ← Matrix.mul_assoc (JS : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.one_mul,
        ← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one]
    have hAm : ∀ m : Fin n → L, (∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ m = (a : Matrix (Fin n) (Fin n) L) *ᵥ t) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) m (fun l => V l j) ∈ Formalism.UG.intL L := by
      rintro m ⟨t, ht, rfl⟩
      rw [hformM, hG, Finset.sum_eq_single j]
      · simp only [Matrix.one_apply_eq, mul_one]; exact hσO _ (ht j)
      · intro k _ hk; simp [Matrix.one_apply_ne hk]
      · intro h; exact absurd (Finset.mem_univ j) h
    obtain ⟨u, w, hu, hxu, hw, he⟩ := T5 L σ n n' JS JT hσσ hσv hJS hJT hS hT x hx (fun l => V l j)
      (fun u hu hxu => hAm u (hN u hu hxu)) (fun w hw => hAm _ (hY w hw))
    obtain ⟨t, ht, het⟩ := (ha _).mp ⟨u, w, hu, hxu, hw, he⟩
    have : (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * V) i j = t i := by
      have h2 : ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (fun l => V l j) = t := by
        rw [het, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [← h2]; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [Matrix.mul_assoc, ← hV, this]; exact ht i
  · intro y'
    constructor
    · rintro ⟨h1, h2⟩ i j
      obtain ⟨u, w, hu, hxu, hw, he⟩ := hcol j
      have : (y' * (a : Matrix (Fin n) (Fin n) L)) i j = (y' *ᵥ (fun k => (a : Matrix (Fin n) (Fin n) L) k j)) i := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [this, he, Matrix.mulVec_add]
      exact Subring.add_mem _ (h1 u hu hxu i) (h2 w hw i)
    · intro h
      refine ⟨fun u hu hxu i => ?_, fun w hw i => ?_⟩
      · obtain ⟨t, ht, rfl⟩ := hN u hu hxu
        rw [Matrix.mulVec_mulVec]; exact iMV _ _ h ht i
      · obtain ⟨t, ht, het⟩ := hY w hw
        rw [het, Matrix.mulVec_mulVec]; exact iMV _ _ h ht i
  · intro v hv
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, w, hu, hxu, hw, he⟩ := (ha _).mpr ⟨t, ht, rfl⟩
      intro i
      rw [he, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      exact Subring.add_mem _ (hxu i) (iMV _ _ hxy hw i)
    · intro hxv
      exact hN v hv hxv
  · intro z
    constructor
    · rintro ⟨t, v, ht, hv, rfl⟩
      obtain ⟨u, w, hu, hxu, hw, he⟩ := (ha _).mpr ⟨t, ht, rfl⟩
      refine ⟨u + v, w, fun i => Subring.add_mem _ (hu i) (hv i), hw, ?_⟩
      rw [he]; abel
    · rintro ⟨v, w, hv, hw, rfl⟩
      obtain ⟨t, ht, het⟩ := hY w hw
      exact ⟨t, v, ht, hv, by rw [het, add_comm]⟩
