import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem conj_app (h : GL (Fin 3) R) (r : D →* GG 3 R) (g : D) :
    conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem conj_comp {D' : Type} [Group D'] (h : GL (Fin 3) R) (r : D →* GG 3 R) (f : D' →* D) :
    (conjBy h r).comp f = conjBy h (r.comp f) := rfl

/- English proof (translation)
Use `ext1 g`. Simplify using `only [conj_app, map_mul, map_inv, _root_.mul_inv_rev, inv_inv]`. Use `group`.
-/
private theorem conj_swap (T h : GL (Fin 3) R) (r : D →* GG 3 R) :
    conjBy (T * h * T⁻¹)⁻¹ (conjBy T r) = conjBy T (conjBy h⁻¹ r) := by
  ext1 g
  simp only [conj_app, map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
  group

/- English proof (translation)
The claim follows from `sub_self _`.
-/
private theorem wt_self (a : Fin 3) : wt a a = 0 := sub_self _

/- English proof (translation)
Rewrite using `[← map_inv, Units.val_mul, Units.val_mul, tor_val, tor_val, Matrix.mul_diagonal, Matrix.diagonal_mul, wt, _root_.zpow_sub, Units.val_mul, _root_.inv_zpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem tor_conj_apply (t : Rˣ) (h : GL (Fin 3) R) (a b : Fin 3) :
    ((tor R t * h * (tor R t)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b =
      ((t ^ wt a b : Rˣ) : R) * (h : Matrix (Fin 3) (Fin 3) R) a b := by
  rw [← map_inv, Units.val_mul, Units.val_mul, tor_val, tor_val, Matrix.mul_diagonal,
    Matrix.diagonal_mul, wt, _root_.zpow_sub, Units.val_mul, _root_.inv_zpow]
  ring

/- English proof (translation)
Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[wt_self, zpow_zero, Units.val_one, one_mul]`. Use `h a a` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply]`. Then use the resulting hypothesis.

Rewrite using `[hY a b hab, sub_zero]`. Apply `Ideal.mul_mem_left` to reduce the goal to its premises. Use `h a b` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, hY a b hab, sub_zero]`. Then use the resulting hypothesis.
-/
private theorem weighted_entry_sub_mem_ideal (I : Ideal R) (t : Rˣ) (X Y : Matrix (Fin 3) (Fin 3) R)
    (hY : ∀ a b, a ≠ b → Y a b = 0) (h : EntIn I (X - Y)) (a b : Fin 3) :
    ((t ^ wt a b : Rˣ) : R) * X a b - Y a b ∈ I := by
  by_cases hab : a = b
  · subst hab
    rw [wt_self, zpow_zero, Units.val_one, one_mul]
    have := h a a
    rwa [Matrix.sub_apply] at this
  · rw [hY a b hab, sub_zero]
    apply Ideal.mul_mem_left
    have := h a b
    rwa [Matrix.sub_apply, hY a b hab, sub_zero] at this

/- English proof (translation)
Introduce `a b`. Rewrite using `[Matrix.sub_apply, tor_conj_apply]`. Conclude with `weighted_entry_sub_mem_ideal _ t _ 1 (fun a b hab => Matrix.one_apply_ne hab) hh a b`.
-/
private theorem inHat_tor [IsLocalRing R] (t : Rˣ) (h : GL (Fin 3) R) (hh : InHat h) :
    InHat (tor R t * h * (tor R t)⁻¹) := by
  intro a b
  rw [Matrix.sub_apply, tor_conj_apply]
  exact weighted_entry_sub_mem_ideal _ t _ 1 (fun a b hab => Matrix.one_apply_ne hab) hh a b

/- English proof (translation)
Take `⟨htri, hine⟩` from `H`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[conj_swap]`. Unfold `Upper at htri ⊢`. Introduce `g hg a b hab`.

Rewrite using `[(conjBy_tor _ t).1 g a b, htri g hg a b hab, mul_zero]`. Introduce `s hs hη a`. Rewrite using `[conj_swap, (conjBy_tor _ t).1 s a a, wt_self, zpow_zero, Units.val_one, one_mul]`. Conclude with `hine s hs hη a`.
-/
private theorem triIn_tor {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} {r : D →* GG 3 R} {h : GL (Fin 3) R}
    (t : Rˣ) (H : TriIn η Ψ I r h) : TriIn η Ψ I (conjBy (tor R t) r) (tor R t * h * (tor R t)⁻¹) := by
  obtain ⟨htri, hine⟩ := H
  refine ⟨?_, ?_⟩
  · rw [conj_swap]
    unfold Upper at htri ⊢
    intro g hg a b hab
    rw [(conjBy_tor _ t).1 g a b, htri g hg a b hab, mul_zero]
  · intro s hs hη a
    rw [conj_swap, (conjBy_tor _ t).1 s a a, wt_self, zpow_zero, Units.val_one, one_mul]
    exact hine s hs hη a

/- English proof (translation)
Take `⟨H1, hlow⟩` from `H`. Use `⟨triIn_tor t H1, ?_⟩` and prove the remaining obligations. Rewrite using `[conj_swap]`. Unfold `Lower at hlow ⊢`. Introduce `g hg a b hab`.

Rewrite using `[(conjBy_tor _ t).1 g a b, hlow g hg a b hab, mul_zero]`.
-/
private theorem diagIn_tor {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} {r : D →* GG 3 R} {h : GL (Fin 3) R}
    (t : Rˣ) (H : DiagIn η Ψ I r h) : DiagIn η Ψ I (conjBy (tor R t) r) (tor R t * h * (tor R t)⁻¹) := by
  obtain ⟨H1, hlow⟩ := H
  refine ⟨triIn_tor t H1, ?_⟩
  rw [conj_swap]
  unfold Lower at hlow ⊢
  intro g hg a b hab
  rw [(conjBy_tor _ t).1 g a b, hlow g hg a b hab, mul_zero]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `O _ _ G Γ ι _ _ _ F R _ _ _ g₁ r t H`. Take `⟨k1, k2, k3, -⟩` from `conjBy_tor r t`. Use `⟨⟨⟨⟨?_, ?_⟩, ?_⟩, k3 _ _ H.norm⟩, ?_⟩` and prove the remaining obligations. Introduce `g`. Rewrite using `[k2, H.mult g]`.

Introduce `g a b`. Rewrite using `[Matrix.sub_apply, k1]`. Use `weighted_entry_sub_mem_ideal _ t _ _ ?_ (H.red g) a b` and prove the remaining obligations. Introduce `a b hab`. Rewrite using `[Matrix.map_apply, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]`.

Introduce `v`. Take `⟨h1, h2, h3⟩` from `H.loc v`. Rewrite using `[conj_comp]`. Use `⟨fun hv => ?_, fun hv => ?_, fun hv s hs => ?_⟩` and prove the remaining obligations. Take `⟨h, hh, ht⟩` from `h1 hv`.

Conclude with `⟨_, inHat_tor t h hh, triIn_tor t ht⟩`. Take `⟨h, hh, ht⟩` from `h2 hv`. Conclude with `⟨_, inHat_tor t h hh, diagIn_tor t ht⟩`. Rewrite using `[conj_app, h3 hv s hs, mul_one, mul_inv_cancel]`. Introduce `n`.

Establish `e : (fun g => (conjBy (tor R t) r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n))) = (fun X : Matrix (Fin 3) (Fin 3) (R ⧸ maximalIdeal R ^ n) => Matrix.of fun a b => Ideal.Quotient.mk (maximalIdeal R ^ n) ((t ^ wt a b : Rˣ) : R) * X a b) ∘ fun g => (r g).mat.map (Ideal.Quotie …`. Use function extensionality and compare the values at `g`. Use extensionality with `a b`. Simplify using `only [Function.comp_apply, Matrix.map_apply, Matrix.of_apply, k1, map_mul]`. Rewrite using `[e]`.

Conclude with `(H.cont n).comp _`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.isPt_tor :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] (g₁ : Γ) (r : Γ →* GG 3 R) (t : Rˣ), F.IsPt g₁ r → F.IsPt g₁ (conjBy (tor R t) r) := by
  intro O _ _ G Γ ι _ _ _ F R _ _ _ g₁ r t H
  obtain ⟨k1, k2, k3, -⟩ := conjBy_tor r t
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, k3 _ _ H.norm⟩, ?_⟩
  · intro g
    rw [k2, H.mult g]
  · intro g a b
    rw [Matrix.sub_apply, k1]
    refine weighted_entry_sub_mem_ideal _ t _ _ ?_ (H.red g) a b
    intro a b hab
    rw [Matrix.map_apply, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]
  · intro v
    obtain ⟨h1, h2, h3⟩ := H.loc v
    rw [conj_comp]
    refine ⟨fun hv => ?_, fun hv => ?_, fun hv s hs => ?_⟩
    · obtain ⟨h, hh, ht⟩ := h1 hv
      exact ⟨_, inHat_tor t h hh, triIn_tor t ht⟩
    · obtain ⟨h, hh, ht⟩ := h2 hv
      exact ⟨_, inHat_tor t h hh, diagIn_tor t ht⟩
    · rw [conj_app, h3 hv s hs, mul_one, mul_inv_cancel]
  · intro n
    have e : (fun g => (conjBy (tor R t) r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n))) =
        (fun X : Matrix (Fin 3) (Fin 3) (R ⧸ maximalIdeal R ^ n) =>
          Matrix.of fun a b => Ideal.Quotient.mk (maximalIdeal R ^ n) ((t ^ wt a b : Rˣ) : R) * X a b) ∘
        fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) := by
      funext g
      ext a b
      simp only [Function.comp_apply, Matrix.map_apply, Matrix.of_apply, k1, map_mul]
    rw [e]
    exact (H.cont n).comp _
