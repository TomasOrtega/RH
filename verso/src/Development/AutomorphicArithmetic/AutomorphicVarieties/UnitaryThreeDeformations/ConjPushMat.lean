import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R R' D : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [Group D]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem map_ofGL (f : R →+* R') (h : GL (Fin 3) R) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
  rfl

/- English proof (translation)
Simplify using `only [conjBy, push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_inv, MulAut.conj_inv_apply, map_mul, map_ofGL]`.
-/
private theorem conj_push (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG 3 R) (g : D) :
    conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (push φ r) g =
      GG.map (φ : R →+* R') (conjBy h⁻¹ r g) := by
  simp only [conjBy, push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_inv, MulAut.conj_inv_apply,
    map_mul, map_ofGL]

/- English proof (translation)
Rewrite using `[conj_push]`. Both sides reduce to the same expression.
-/
private theorem conj_push_mat (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG 3 R) (g : D) (a b : Fin 3) :
    (conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (push φ r) g).mat a b =
      φ ((conjBy h⁻¹ r g).mat a b) := by
  rw [conj_push]; rfl

/- English proof (translation)
Take `⟨htri, hine⟩` from `H`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `Upper at htri ⊢`. Introduce `g hg a b hab`. Rewrite using `[conj_push_mat, htri g hg a b hab, map_zero]`.

Introduce `s hs hη a`. Rewrite using `[conj_push_mat, hine s hs hη a, AlgHom.commutes]`.
-/
private theorem triIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG 3 R} {h : GL (Fin 3) R} (H : TriIn η Ψ I r h) :
    TriIn η Ψ I (push φ r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  obtain ⟨htri, hine⟩ := H
  refine ⟨?_, ?_⟩
  · unfold Upper at htri ⊢
    intro g hg a b hab
    rw [conj_push_mat, htri g hg a b hab, map_zero]
  · intro s hs hη a
    rw [conj_push_mat, hine s hs hη a, AlgHom.commutes]

/- English proof (translation)
Take `⟨H1, hlow⟩` from `H`. Use `⟨triIn_push φ H1, ?_⟩` and prove the remaining obligations. Unfold `Lower at hlow ⊢`. Introduce `g hg a b hab`. Rewrite using `[conj_push_mat, hlow g hg a b hab, map_zero]`.
-/
private theorem diagIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG 3 R} {h : GL (Fin 3) R} (H : DiagIn η Ψ I r h) :
    DiagIn η Ψ I (push φ r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  obtain ⟨H1, hlow⟩ := H
  refine ⟨triIn_push φ H1, ?_⟩
  unfold Lower at hlow ⊢
  intro g hg a b hab
  rw [conj_push_mat, hlow g hg a b hab, map_zero]

variable [IsLocalRing R] [IsLocalRing R']

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun hu => hx (isUnit_of_map_unit φ x hu)`.
-/
private theorem map_mem_max (φ : R →ₐ[O] R') [IsLocalHom φ] {x : R} (hx : x ∈ maximalIdeal R) :
    φ x ∈ maximalIdeal R' := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun hu => hx (isUnit_of_map_unit φ x hu)

/- English proof (translation)
Unfold `InHat CongOne EntIn at *`. Introduce `a b`. Establish `e : ((GeneralLinearGroup.map (φ : R →+* R') h : Matrix (Fin 3) (Fin 3) R') - 1) a b = φ (((h : Matrix (Fin 3) (Fin 3) R) - 1) a b)`. Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, map_sub]`. Use `congr 1`.

Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e]`. Conclude with `map_mem_max φ (H a b)`.
-/
private theorem inHat_push (φ : R →ₐ[O] R') [IsLocalHom φ] {h : GL (Fin 3) R} (H : InHat h) :
    InHat (GeneralLinearGroup.map (φ : R →+* R') h) := by
  unfold InHat CongOne EntIn at *
  intro a b
  have e : ((GeneralLinearGroup.map (φ : R →+* R') h : Matrix (Fin 3) (Fin 3) R') - 1) a b =
      φ (((h : Matrix (Fin 3) (Fin 3) R) - 1) a b) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  exact map_mem_max φ (H a b)

/- English proof (translation)
Unfold `UpperTheory.V.UnitaryThreeInertia.AdicCont at *`. Introduce `n`. Establish `hle : ∀ x ∈ maximalIdeal R ^ n, (φ : R →+* R') x ∈ maximalIdeal R' ^ n`. Introduce `x hx`. Establish `h1 : Ideal.map (φ : R →+* R') (maximalIdeal R) ≤ maximalIdeal R'`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `y hy`. Conclude with `map_mem_max φ hy`. Establish `h2 : Ideal.map (φ : R →+* R') (maximalIdeal R ^ n) ≤ maximalIdeal R' ^ n`. Rewrite using `[Ideal.map_pow]`.

Conclude with `Ideal.pow_right_mono h1 n`. Conclude with `h2 (Ideal.mem_map_of_mem _ hx)`. Set `ψ : R ⧸ maximalIdeal R ^ n →+* R' ⧸ maximalIdeal R' ^ n` to `Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (φ : R →+* R')) (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hle x hx))`. Establish `hfun : (fun g => ((push φ r) g).mat.map (Ideal.Quotient.mk (maximalIdeal R' ^ n))) = (fun M => M.map ψ) ∘ (fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n)))`. Use function extensionality and compare the values at `g`.

Use extensionality with `a b`. Simplify using `only [Function.comp_apply, Matrix.map_apply, ψ, Ideal.Quotient.lift_mk, RingHom.comp_apply]`. Both sides reduce to the same expression. Rewrite using `[hfun]`. Conclude with `(H n).comp _`.
-/
private theorem adicCont_push [TopologicalSpace D] (φ : R →ₐ[O] R') [IsLocalHom φ] {r : D →* GG 3 R}
    (H : AdicCont (maximalIdeal R) r) : AdicCont (maximalIdeal R') (push φ r) := by
  unfold UpperTheory.V.UnitaryThreeInertia.AdicCont at *
  intro n
  have hle : ∀ x ∈ maximalIdeal R ^ n, (φ : R →+* R') x ∈ maximalIdeal R' ^ n := by
    intro x hx
    have h1 : Ideal.map (φ : R →+* R') (maximalIdeal R) ≤ maximalIdeal R' := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact map_mem_max φ hy
    have h2 : Ideal.map (φ : R →+* R') (maximalIdeal R ^ n) ≤ maximalIdeal R' ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono h1 n
    exact h2 (Ideal.mem_map_of_mem _ hx)
  let ψ : R ⧸ maximalIdeal R ^ n →+* R' ⧸ maximalIdeal R' ^ n :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (φ : R →+* R'))
      (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hle x hx))
  have hfun : (fun g => ((push φ r) g).mat.map (Ideal.Quotient.mk (maximalIdeal R' ^ n))) =
      (fun M => M.map ψ) ∘ (fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n))) := by
    funext g
    ext a b
    simp only [Function.comp_apply, Matrix.map_apply, ψ, Ideal.Quotient.lift_mk, RingHom.comp_apply]
    rfl
  rw [hfun]
  exact (H n).comp _

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `O _ _ G Γ ι _ _ _ F R R' _ _ _ _ _ _ φ _ g₁ r hr`. Establish `hmat : ∀ x : GG 3 R, ((GG.map (φ : R →+* R')) x).mat = x.mat.map φ` using `fun x => rfl`. Establish `hpm : ∀ g, ((push φ r) g).mat = (r g).mat.map φ` using `fun g => hmat (r g)`. Use `⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, adicCont_push φ hr.cont⟩` and prove the remaining obligations. Establish `hm` using `hr.mult`.

Unfold `HasMult at hm ⊢`. Introduce `g`. Conclude with `hm g`. Introduce `g a b`. Rewrite using `[Matrix.sub_apply, hpm, Matrix.map_apply, Matrix.map_apply, ← AlgHom.commutes φ, ← map_sub]`.

Apply `map_mem_max φ` to reduce the goal to its premises. Use `hr.red g a b` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, Matrix.map_apply]`. Then use the resulting hypothesis. Introduce `v`. Establish `hv` using `hr.loc v`.

Unfold `Frame.LocAt at hv ⊢`. Take `⟨hT, hD, hU⟩` from `hv`. Unfold `CondT CondD CondU at *`. Establish `hcomp : (push φ r).comp (F.loc v) = push φ (r.comp (F.loc v))` using `rfl`. Rewrite using `[hcomp]`.

Use `⟨fun h => ?_, fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Take `⟨k, hk, htr⟩` from `hT h`. Conclude with `⟨_, inHat_push φ hk, triIn_push φ htr⟩`. Take `⟨k, hk, hdi⟩` from `hD h`. Conclude with `⟨_, inHat_push φ hk, diagIn_push φ hdi⟩`.

Introduce `s hs show (GG.map (φ : R →+* R')) ((r.comp (F.loc v)) s) = 1`. Rewrite using `[hU h s hs, map_one]`. Take `⟨hatc, hz12, hz21⟩` from `hr.norm`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hpm, hatc, Matrix.map_one _ (map_zero φ) (map_one φ)]`.

Unfold `zmat at hz12 ⊢`. Rewrite using `[Matrix.sub_apply, hpm, hpm, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, hz12, map_zero]`. Unfold `zmat at hz21 ⊢`. Rewrite using `[Matrix.sub_apply, hpm, hpm, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, hz21, map_zero]`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.isPt_push :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) {R R' : Type} [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing R'] [IsLocalRing R'] [Algebra O R'] (φ : R →ₐ[O] R') [IsLocalHom φ] (g₁ : Γ) (r : Γ →* GG 3 R), F.IsPt g₁ r → F.IsPt g₁ (push φ r) := by
  intro O _ _ G Γ ι _ _ _ F R R' _ _ _ _ _ _ φ _ g₁ r hr
  have hmat : ∀ x : GG 3 R, ((GG.map (φ : R →+* R')) x).mat = x.mat.map φ := fun x => rfl
  have hpm : ∀ g, ((push φ r) g).mat = (r g).mat.map φ := fun g => hmat (r g)
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, adicCont_push φ hr.cont⟩
  · have hm := hr.mult
    unfold HasMult at hm ⊢
    intro g
    exact hm g
  · intro g a b
    rw [Matrix.sub_apply, hpm, Matrix.map_apply, Matrix.map_apply, ← AlgHom.commutes φ, ← map_sub]
    apply map_mem_max φ
    have := hr.red g a b
    rwa [Matrix.sub_apply, Matrix.map_apply] at this
  · intro v
    have hv := hr.loc v
    unfold Frame.LocAt at hv ⊢
    obtain ⟨hT, hD, hU⟩ := hv
    unfold CondT CondD CondU at *
    have hcomp : (push φ r).comp (F.loc v) = push φ (r.comp (F.loc v)) := rfl
    rw [hcomp]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨k, hk, htr⟩ := hT h
      exact ⟨_, inHat_push φ hk, triIn_push φ htr⟩
    · obtain ⟨k, hk, hdi⟩ := hD h
      exact ⟨_, inHat_push φ hk, diagIn_push φ hdi⟩
    · intro s hs
      show (GG.map (φ : R →+* R')) ((r.comp (F.loc v)) s) = 1
      rw [hU h s hs, map_one]
  · obtain ⟨hatc, hz12, hz21⟩ := hr.norm
    refine ⟨?_, ?_, ?_⟩
    · rw [hpm, hatc, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · unfold zmat at hz12 ⊢
      rw [Matrix.sub_apply, hpm, hpm, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, hz12,
        map_zero]
    · unfold zmat at hz21 ⊢
      rw [Matrix.sub_apply, hpm, hpm, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, hz21,
        map_zero]
