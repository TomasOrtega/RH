import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne

noncomputable section

namespace GlobalTheory.TamOne.IdealLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mulVec_intLoc_smul {v : HeightOneSpectrum (𝓞 F)} (N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (c : intLoc F E v) (w : Fin n → Fv F v ⊗[F] E) : N *ᵥ (c • w) = c • (N *ᵥ w) := by
  funext i
  change (N *ᵥ fun j => (c : Fv F v ⊗[F] E) * w j) i = (c : Fv F v ⊗[F] E) * (N *ᵥ w) i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem incl_smul_tmul {v : HeightOneSpectrum (𝓞 F)} (s : 𝓞 E) (a : Fv F v) (x : Fin n → E) :
    intLocIncl (E := E) v s • (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (s • x) i := by
  funext i
  change ((1 : Fv F v) ⊗ₜ[F] (s : E)) * (a ⊗ₜ[F] x i) = a ⊗ₜ[F] ((s : E) * x i)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem incl_smul_mem_latLoc (L : Submodule (𝓞 E) (Fin n → E)) (𝔞 : Ideal (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    {s : 𝓞 E} (hs : s ∈ 𝔞) {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc F L v) :
    intLocIncl (E := E) v s • w ∈ latLoc F (𝔞 • L) v := by
  refine latLoc_induction (p := fun w => intLocIncl (E := E) v s • w ∈ latLoc F (𝔞 • L) v)
    (fun a ha x hx => ?_) (by rw [smul_zero]; exact zero_mem _)
    (fun y z hy hz => by rw [smul_add]; exact add_mem hy hz)
    (fun y hy => by rw [smul_neg]; exact neg_mem hy) hw
  rw [incl_smul_tmul]
  exact tmul_mem_latLoc ha (Submodule.smul_mem_smul hs hx)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Separate the alternatives or extract the components of the hypothesis. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem latLoc_smul_iff_of_frame (L : Submodule (𝓞 E) (Fin n → E)) (𝔞 : Ideal (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (h : GL (Fin n) (Fv F v ⊗[F] E))
    (hh : ∀ z : Fin n → Fv F v ⊗[F] E, z ∈ latLoc F L v ↔
      ∀ i, (((h⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ z) i ∈ intLoc F E v)
    (z : Fin n → Fv F v ⊗[F] E) :
    z ∈ latLoc F (𝔞 • L) v ↔ ∀ i, ∃ t ∈ 𝔞.map (intLocIncl (E := E) v),
      ((t : intLoc F E v) : Fv F v ⊗[F] E) =
        (((h⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ z) i := by
  set M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := ((h⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hM
  set I : Ideal (intLoc F E v) := 𝔞.map (intLocIncl (E := E) v) with hI
  constructor
  · intro hz
    refine latLoc_induction (p := fun z => ∀ i, ∃ t ∈ I, ((t : intLoc F E v) : Fv F v ⊗[F] E) = (M *ᵥ z) i)
      (fun a ha x hx => ?_) (fun i => ⟨0, zero_mem _, by simp⟩) (fun y z hy hz i => ?_) (fun y hy i => ?_) hz
    · refine Submodule.smul_induction_on hx
        (p := fun x => ∀ i, ∃ t ∈ I, ((t : intLoc F E v) : Fv F v ⊗[F] E) = (M *ᵥ fun i => a ⊗ₜ[F] x i) i)
        (fun s hs y hy i => ?_) (fun x y hx hy i => ?_)
      · have hw := (hh _).1 (tmul_mem_latLoc ha hy) i
        refine ⟨intLocIncl v s * ⟨_, hw⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hs), ?_⟩
        rw [← incl_smul_tmul, mulVec_intLoc_smul]
        rfl
      · obtain ⟨t, ht, e⟩ := hx i
        obtain ⟨t', ht', e'⟩ := hy i
        refine ⟨t + t', add_mem ht ht', ?_⟩
        have : (fun i => a ⊗ₜ[F] (x + y) i) = (fun i => a ⊗ₜ[F] x i) + fun i => a ⊗ₜ[F] y i :=
          funext fun i => TensorProduct.tmul_add _ _ _
        rw [this, Matrix.mulVec_add, Pi.add_apply, ← e, ← e']
        rfl
    · obtain ⟨t, ht, e⟩ := hy i
      obtain ⟨t', ht', e'⟩ := hz i
      refine ⟨t + t', add_mem ht ht', ?_⟩
      rw [Matrix.mulVec_add, Pi.add_apply, ← e, ← e']
      rfl
    · obtain ⟨t, ht, e⟩ := hy i
      refine ⟨-t, neg_mem ht, ?_⟩
      rw [Matrix.mulVec_neg, Pi.neg_apply, ← e]
      rfl
  · intro ht
    have hz : z = (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ (M *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, hM, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hz, ← Finset.univ_sum_single (M *ᵥ z), Matrix.mulVec_sum]
    refine sum_mem fun i _ => ?_
    obtain ⟨t, htI, e⟩ := ht i
    rw [← e]
    have h1 : (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Pi.single i 1 ∈ latLoc F L v := by
      refine (hh _).2 fun j => ?_
      rw [Matrix.mulVec_mulVec, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rcases eq_or_ne j i with rfl | hj
      · rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
    have hsingle : ∀ c : intLoc F E v, Pi.single i ((c : intLoc F E v) : Fv F v ⊗[F] E) =
        c • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) := by
      intro c
      funext j
      rcases eq_or_ne j i with rfl | hj
      · change _ = (c : Fv F v ⊗[F] E) * _
        rw [Pi.single_eq_same, Pi.single_eq_same, mul_one]
      · change _ = (c : Fv F v ⊗[F] E) * _
        rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, mul_zero]
    rw [hsingle, mulVec_intLoc_smul]
    have : t ∈ Submodule.span (intLoc F E v) (intLocIncl (E := E) v '' (𝔞 : Set (𝓞 E))) := htI
    refine Submodule.span_induction
      (p := fun t _ => t • ((h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Pi.single i 1) ∈ latLoc F (𝔞 • L) v)
      ?_ ?_ ?_ ?_ this
    · rintro _ ⟨s, hs, rfl⟩
      exact incl_smul_mem_latLoc L 𝔞 v hs h1
    · rw [zero_smul]; exact zero_mem _
    · intro x y _ _ hx hy
      rw [add_smul]; exact add_mem hx hy
    · intro c x _ hx
      rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.TamOne.IdealLoc
