import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open PositivityTheory.Rg.Tf.Loc

/- English proof (translation)
Introduce `hC k E _ _ _ _ _ σ hσ n δ γ hγ hN`. Establish `hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1`. Rewrite using `[← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]`. Establish `hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable`. Establish `: ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k E)` using `rfl`.

Rewrite using `[this, Matrix.charpoly_map]`. Conclude with `hγ.map`. Establish `hfix : ∀ y : GL (Fin n) k, sigmaGL σ (incl y : GL (Fin n) E) = incl y` using `fun y => by`. Use extensionality with `i j`. Conclude with `σ.commutes _`.

Establish `hcomm : ∀ a b : GL (Fin n) E, a * incl γ = incl γ * a → b * incl γ = incl γ * b → a * b = b * a` using `fun a b ha hb => Units.ext (hC E n _ a.val b.val hsep (congrArg Units.val ha) (congrArg Units.val hb))`. Establish `hδ : δ * incl γ = incl γ * δ`. Establish `h` using `map_twNorm_of_pow_eq_one (sigmaGL σ) hp δ`. Express the relevant statement in the definitionally equal form `sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ at h`. Rewrite `h` using `[hN, hfix]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨by rw [IsTwRegSemisimple, hN]; exact hsep, Subgroup.ext fun x => ⟨fun hx => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : x * incl γ = incl γ * x` using `hN ▸ twCent_commute_twNorm _ hp δ hx`. Establish `h2 : x⁻¹ * δ * sigmaGL σ x = δ` using `hx`. Establish `h3 : sigmaGL σ x = x`.

Combine the equalities or inequalities in the displayed calculation. Establish `h4 : ∀ i j, ∃ c, algebraMap k E c = (x : Matrix (Fin n) (Fin n) E) i j` using `fun i j => by`. Establish `hs : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) ((x : Matrix (Fin n) (Fin n) E) i j)` using `congrArg (fun y : GL (Fin n) E => (y : Matrix (Fin n) (Fin n) E) i j) h3`. Use `(IsGalois.mem_bot_iff_fixed ((x : Matrix (Fin n) (Fin n) E) i j)).mpr fun τ => (Subgroup.zpowers_le.mpr hs) (hσ τ)` as an intermediate fact. Rewrite `this` using `[IntermediateField.mem_bot]`. Then use the resulting hypothesis.

Use `choose M hM using h4`. Establish `e : (algebraMap k E).mapMatrix (Matrix.of M) = (x : Matrix (Fin n) (Fin n) E)`. Use extensionality with `i j`. Conclude with `hM i j`. Establish `hd : (Matrix.of M).det ≠ 0` using `fun h0 => by`.

Establish `h1` using `RingHom.map_det (algebraMap k E) (Matrix.of M)`. Rewrite `h1` using `[h0, map_zero, e]`. Conclude with `(Matrix.GeneralLinearGroup.det x).ne_zero h1.symm`. Establish `e' : incl (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) = x` using `Units.ext e`. Use `⟨_, Subgroup.mem_centralizer_singleton_iff.2 ?_, e'⟩` and prove the remaining obligations.

Establish `hinj : Function.Injective (incl : GL (Fin n) k → GL (Fin n) E)` using `fun a b h => by`. Use extensionality with `i j`. Conclude with `(algebraMap k E).injective (congrArg (fun y : GL (Fin n) E => (y : Matrix (Fin n) (Fin n) E) i j) h)`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, e', h1]`.

Introduce and unpack `⟨t, ht, rfl⟩`. Establish `h1 : (incl t : GL (Fin n) E) * incl γ = incl γ * incl t`. Rewrite using `[← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 ht]`. Rewrite using `[mem_twCent, hfix, mul_assoc, ← hcomm _ δ h1 hδ]`. Use `group`.
-/
theorem UpperTheory.V.Z.Tf.Orb.twCentImg :
    UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCentImg := by
  intro hC k E _ _ _ _ _ σ hσ n δ γ hγ hN
  have hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    have : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k E) := rfl
    rw [this, Matrix.charpoly_map]
    exact hγ.map
  have hfix : ∀ y : GL (Fin n) k, sigmaGL σ (incl y : GL (Fin n) E) = incl y := fun y => by
    ext i j
    exact σ.commutes _
  have hcomm : ∀ a b : GL (Fin n) E, a * incl γ = incl γ * a → b * incl γ = incl γ * b → a * b = b * a := fun a b ha hb =>
    Units.ext (hC E n _ a.val b.val hsep (congrArg Units.val ha) (congrArg Units.val hb))
  have hδ : δ * incl γ = incl γ * δ := by
    have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hp δ
    change sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ at h
    rw [hN, hfix] at h
    calc δ * incl γ = δ * (δ⁻¹ * incl γ * δ) := by rw [← h]
      _ = incl γ * δ := by group
  refine ⟨by rw [IsTwRegSemisimple, hN]; exact hsep, Subgroup.ext fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : x * incl γ = incl γ * x := hN ▸ twCent_commute_twNorm _ hp δ hx
    have h2 : x⁻¹ * δ * sigmaGL σ x = δ := hx
    have h3 : sigmaGL σ x = x := by
      calc sigmaGL σ x = δ⁻¹ * x * (x⁻¹ * δ * sigmaGL σ x) := by group
        _ = δ⁻¹ * (x * δ) := by rw [h2, mul_assoc]
        _ = x := by rw [hcomm x δ h1 hδ]; group
    have h4 : ∀ i j, ∃ c, algebraMap k E c = (x : Matrix (Fin n) (Fin n) E) i j := fun i j => by
      have hs : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) ((x : Matrix (Fin n) (Fin n) E) i j) :=
        congrArg (fun y : GL (Fin n) E => (y : Matrix (Fin n) (Fin n) E) i j) h3
      have := (IsGalois.mem_bot_iff_fixed ((x : Matrix (Fin n) (Fin n) E) i j)).mpr fun τ =>
        (Subgroup.zpowers_le.mpr hs) (hσ τ)
      rwa [IntermediateField.mem_bot] at this
    choose M hM using h4
    have e : (algebraMap k E).mapMatrix (Matrix.of M) = (x : Matrix (Fin n) (Fin n) E) := by
      ext i j
      exact hM i j
    have hd : (Matrix.of M).det ≠ 0 := fun h0 => by
      have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
      rw [h0, map_zero, e] at h1
      exact (Matrix.GeneralLinearGroup.det x).ne_zero h1.symm
    have e' : incl (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) = x := Units.ext e
    refine ⟨_, Subgroup.mem_centralizer_singleton_iff.2 ?_, e'⟩
    have hinj : Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := fun a b h => by
      ext i j
      exact (algebraMap k E).injective (congrArg (fun y : GL (Fin n) E => (y : Matrix (Fin n) (Fin n) E) i j) h)
    apply hinj
    rw [map_mul, map_mul, e', h1]
  · rintro ⟨t, ht, rfl⟩
    have h1 : (incl t : GL (Fin n) E) * incl γ = incl γ * incl t := by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 ht]
    rw [mem_twCent, hfix, mul_assoc, ← hcomm _ δ h1 hδ]
    group
