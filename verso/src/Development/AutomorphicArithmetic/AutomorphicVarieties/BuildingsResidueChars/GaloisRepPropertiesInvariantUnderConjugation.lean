import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.S2

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Take `⟨h1, -, h3⟩` from `hr`. Use `⟨h1, fun _ _ _ => Submodule.mem_top, fun W _ hi => ?_⟩` and prove the remaining obligations. Establish `key` using `h3 (W.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) le_top (fun s v hv => by`. Establish `h4` using `hi s _ hv`.

Rewrite `h4` using `[hg s]`. Simplify `h4)` using `[Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Establish `hs : Function.Surjective (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))` using `fun v => ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v, by`. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩`. Establish `e` using `Submodule.map_comap_eq_of_surjective hs W`.

Break down `key with key | key` into its components or cases. Use `left`. Rewrite using `[← e, key, Submodule.map_bot]`. Use `right`. Rewrite using `[← e, key, Submodule.map_top, LinearMap.range_eq_top.mpr hs]`.
-/
private theorem isIrr_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨h1, -, h3⟩ := hr
  refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W _ hi => ?_⟩
  have key := h3 (W.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) le_top (fun s v hv => by
    have h4 := hi s _ hv
    rw [hg s] at h4
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4)
  have hs : Function.Surjective (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)) := fun v =>
    ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v, by
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  have e := Submodule.map_comap_eq_of_surjective hs W
  rcases key with key | key
  · left
    rw [← e, key, Submodule.map_bot]
  · right
    rw [← e, key, Submodule.map_top, LinearMap.range_eq_top.mpr hs]

/- English proof (translation)
Introduce `W hW`. Take `⟨-, -, h3⟩` from `h ⊤ (by simp)`. Break down `h3 W le_top (fun s v hv => hW s v hv) with e | e` into its components or cases. Conclude with `⟨⊤, fun _ _ _ => Submodule.mem_top, e ▸ isCompl_bot_top⟩`. Use `⟨⊥, fun s v hv => ?_, e ▸ isCompl_top_bot⟩` and prove the remaining obligations.

Rewrite `hv`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hv, Matrix.mulVec_zero]`.
-/
private theorem ss_of_irrOpen {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k}
    (h : IrrOpen r) : IsSSRep r := by
  intro W hW
  obtain ⟨-, -, h3⟩ := h ⊤ (by simp)
  rcases h3 W le_top (fun s v hv => hW s v hv) with e | e
  · exact ⟨⊤, fun _ _ _ => Submodule.mem_top, e ▸ isCompl_bot_top⟩
  · refine ⟨⊥, fun s v hv => ?_, e ▸ isCompl_top_bot⟩
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, Matrix.mulVec_zero]

/- English proof (translation)
Take `⟨κ, h1, h2⟩` from `H`. Conclude with `⟨κ, h1.of_iso h, h2⟩`.
-/
private theorem ordAt_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r r' : G F Ω →* GL (Fin n) (Qbar l)} {m : Fin n → ℤ} {ψ : Fin n → G F Ω →* (Qbar l)ˣ} {A : ValuationSubring Ω}
    (h : RepIso r r') (H : OrdAt r m ψ A) : OrdAt r' m ψ A := by
  obtain ⟨κ, h1, h2⟩ := H
  exact ⟨κ, h1.of_iso h, h2⟩

/- English proof (translation)
Introduce `U hU` and use `by obtain ⟨g, hg⟩ := h have e : RepIso (r.comp U.subtype) (r'.comp U.subtype) := ⟨g, fun s => hg s⟩ exact isIrr_iso e (H U hU)`.
-/
private theorem irrOpen_iso {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}
    (h : RepIso r r') (H : IrrOpen r) : IrrOpen r' := fun U hU => by
  obtain ⟨g, hg⟩ := h
  have e : RepIso (r.comp U.subtype) (r'.comp U.subtype) := ⟨g, fun s => hg s⟩
  exact isIrr_iso e (H U hU)

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Use `MonoidHom.ext fun s => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply, hg, map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det (r s)), mul_inv_cancel_right]`.
-/
private theorem det_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r') :
    Matrix.GeneralLinearGroup.det.comp r' = Matrix.GeneralLinearGroup.det.comp r := by
  obtain ⟨g, hg⟩ := h
  refine MonoidHom.ext fun s => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hg, map_mul, map_mul, map_inv,
    mul_comm _ (Matrix.GeneralLinearGroup.det (r s)), mul_inv_cancel_right]

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Introduce `s i`. Rewrite using `[hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`. Conclude with `H s i`.
-/
private theorem resSum_iso {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {n : ℕ} {r r' : Γ →* GL (Fin n) (Qbar l)}
    {χ : Fin n → Γ →* (Qbar l)ˣ} (h : RepIso r r') (H : ResSum r χ) : ResSum r' χ := by
  obtain ⟨g, hg⟩ := h
  intro s i
  rw [hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  exact H s i

/- English proof (translation)
Use `⟨hs, H.2.mono fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨B, b1, b2⟩` from `hw`. Conclude with `⟨B, b1, b2.of_iso h⟩`.
-/
private theorem attR_iso {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {ι : Qbar l ≃+* ℂ} {π} (h : RepIso r r')
    (hs : IsSSRep r') (H : AttR ι r π) : AttR ι r' π := by
  refine ⟨hs, H.2.mono fun w hw => ?_⟩
  obtain ⟨B, b1, b2⟩ := hw
  exact ⟨B, b1, b2.of_iso h⟩

/- English proof (translation)
Introduce `A hA` and use `(H A hA).of_iso h`.
-/
private theorem away_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r r' : G F Ω →* GL (Fin n) (Qbar l)} {τ : Fin n → G F Ω →* (Qbar l)ˣ}
    (h : RepIso r r') (H : TypeAway r τ) : TypeAway r' τ := fun A hA => (H A hA).of_iso h

/- English proof (translation)
Introduce `Ω _ _ _ l _ k₀ _ _ ι x k t r r' H h`. Establish `hirr : IrrOpen r'` using `irrOpen_iso h H.irr`. Take `⟨π, h2, h3⟩` from `H.att`. Use `⟨H.hk, H.ht, H.dvd, continuous_of_iso H.cont h, hirr, ⟨π, attR_iso h (ss_of_irrOpen hirr) h2, h3⟩, (det_iso h).trans H.det, resSum_iso h H.res, away_iso h H.away, ?_⟩` and prove the remaining obligations. Introduce `A A' hA g hg hy`.

Break down `H.above A A' hA g hg hy with a | a` into its components or cases. Conclude with `Or.inl ⟨ordAt_iso h a.1, ordAt_iso h a.2⟩`. Conclude with `Or.inr ⟨ordAt_iso h a.1, ordAt_iso h a.2⟩`.
-/
theorem UpperTheory.galoisRep_properties_invariant_under_conjugation :
    UpperTheory.V.Sd.S2.MixConj := by
  intro Ω _ _ _ l _ k₀ _ _ ι x k t r r' H h
  have hirr : IrrOpen r' := irrOpen_iso h H.irr
  obtain ⟨π, h2, h3⟩ := H.att
  refine ⟨H.hk, H.ht, H.dvd, continuous_of_iso H.cont h, hirr, ⟨π, attR_iso h (ss_of_irrOpen hirr) h2, h3⟩,
    (det_iso h).trans H.det, resSum_iso h H.res, away_iso h H.away, ?_⟩
  intro A A' hA g hg hy
  rcases H.above A A' hA g hg hy with a | a
  · exact Or.inl ⟨ordAt_iso h a.1, ordAt_iso h a.2⟩
  · exact Or.inr ⟨ordAt_iso h a.1, ordAt_iso h a.2⟩
