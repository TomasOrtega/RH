import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne

noncomputable section

namespace GlobalTheory.TamOne.IdealLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(N *ᵥ fun j => (c : Fv F v ⊗[F] E) * w j) i = (c : Fv F v ⊗[F] E) * (N *ᵥ w) i`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem mulVec_intLoc_smul {v : HeightOneSpectrum (𝓞 F)} (N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (c : intLoc F E v) (w : Fin n → Fv F v ⊗[F] E) : N *ᵥ (c • w) = c • (N *ᵥ w) := by
  funext i
  change (N *ᵥ fun j => (c : Fv F v ⊗[F] E) * w j) i = (c : Fv F v ⊗[F] E) * (N *ᵥ w) i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `((1 : Fv F v) ⊗ₜ[F] (s : E)) * (a ⊗ₜ[F] x i) = a ⊗ₜ[F] ((s : E) * x i)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem incl_smul_tmul {v : HeightOneSpectrum (𝓞 F)} (s : 𝓞 E) (a : Fv F v) (x : Fin n → E) :
    intLocIncl (E := E) v s • (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (s • x) i := by
  funext i
  change ((1 : Fv F v) ⊗ₜ[F] (s : E)) * (a ⊗ₜ[F] x i) = a ⊗ₜ[F] ((s : E) * x i)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
Use `latLoc_induction (p := fun w => intLocIncl (E := E) v s • w ∈ latLoc F (𝔞 • L) v) (fun a ha x hx => ?_) (by rw [smul_zero]; exact zero_mem _) (fun y z hy hz => by rw [smul_add]; exact add_mem hy hz) (fun y hy => by rw [smul_neg]; exact neg_mem hy) hw` and prove the remaining obligations. Rewrite using `[incl_smul_tmul]`. Conclude with `tmul_mem_latLoc ha (Submodule.smul_mem_smul hs hx)`.
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
Use `set M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := ((h⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hM`. Use `set I : Ideal (intLoc F E v) := 𝔞.map (intLocIncl (E := E) v) with hI`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Use `latLoc_induction (p := fun z => ∀ i, ∃ t ∈ I, ((t : intLoc F E v) : Fv F v ⊗[F] E) = (M *ᵥ z) i) (fun a ha x hx => ?_) (fun i => ⟨0, zero_mem _, by simp⟩) (fun y z hy hz i => ?_) (fun y hy i => ?_) hz` and prove the remaining obligations.

Use `Submodule.smul_induction_on hx (p := fun x => ∀ i, ∃ t ∈ I, ((t : intLoc F E v) : Fv F v ⊗[F] E) = (M *ᵥ fun i => a ⊗ₜ[F] x i) i) (fun s hs y hy i => ?_) (fun x y hx hy i => ?_)` and prove the remaining obligations. Establish `hw` using `(hh _).1 (tmul_mem_latLoc ha hy) i`. Use `⟨intLocIncl v s * ⟨_, hw⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hs), ?_⟩` and prove the remaining obligations. Rewrite using `[← incl_smul_tmul, mulVec_intLoc_smul]`. Both sides reduce to the same expression.

Take `⟨t, ht, e⟩` from `hx i`. Take `⟨t', ht', e'⟩` from `hy i`. Use `⟨t + t', add_mem ht ht', ?_⟩` and prove the remaining obligations. Establish `: (fun i => a ⊗ₜ[F] (x + y) i) = (fun i => a ⊗ₜ[F] x i) + fun i => a ⊗ₜ[F] y i`. Use function extensionality and compare the values at `fun i => TensorProduct.tmul_add _ _ _`.

Rewrite using `[this, Matrix.mulVec_add, Pi.add_apply, ← e, ← e']`. Both sides reduce to the same expression. Take `⟨t, ht, e⟩` from `hy i`. Take `⟨t', ht', e'⟩` from `hz i`. Use `⟨t + t', add_mem ht ht', ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_add, Pi.add_apply, ← e, ← e']`. Both sides reduce to the same expression. Take `⟨t, ht, e⟩` from `hy i`. Use `⟨-t, neg_mem ht, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_neg, Pi.neg_apply, ← e]`.

Both sides reduce to the same expression. Introduce `ht`. Establish `hz : z = (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ (M *ᵥ z)`. Rewrite using `[Matrix.mulVec_mulVec, hM, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[hz, ← Finset.univ_sum_single (M *ᵥ z), Matrix.mulVec_sum]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Take `⟨t, htI, e⟩` from `ht i`. Rewrite using `[← e]`. Establish `h1 : (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Pi.single i 1 ∈ latLoc F L v`. Use `(hh _).2 fun j => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_mulVec, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Break down `eq_or_ne j i with rfl | hj` into its components or cases. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne hj]`.

Conclude with `zero_mem _`. Establish `hsingle : ∀ c : intLoc F E v, Pi.single i ((c : intLoc F E v) : Fv F v ⊗[F] E) = c • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E)`. Introduce `c`. Use function extensionality and compare the values at `j`. Break down `eq_or_ne j i with rfl | hj` into its components or cases.

Express the relevant statement in the definitionally equal form `_ = (c : Fv F v ⊗[F] E) * _`. Rewrite using `[Pi.single_eq_same, Pi.single_eq_same, mul_one]`. Express the relevant statement in the definitionally equal form `_ = (c : Fv F v ⊗[F] E) * _`. Rewrite using `[Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, mul_zero]`. Rewrite using `[hsingle, mulVec_intLoc_smul]`.

Establish `: t ∈ Submodule.span (intLoc F E v) (intLocIncl (E` using `E) v '' (𝔞 : Set (𝓞 E))) := htI`. Use `Submodule.span_induction (p := fun t _ => t • ((h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Pi.single i 1) ∈ latLoc F (𝔞 • L) v) ?_ ?_ ?_ ?_ this` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `incl_smul_mem_latLoc L 𝔞 v hs h1`. Rewrite using `[zero_smul]`.

Conclude with `zero_mem _`. Introduce `x y _ _ hx hy`. Rewrite using `[add_smul]`. Conclude with `add_mem hx hy`. Introduce `c x _ hx`.

Rewrite using `[smul_eq_mul, mul_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
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
