import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.ToIdeleSq
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqTopOfIrreducibleOverAlgClosed
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.EG GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.DirichletHecke
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)

/- English proof (translation)
Take `⟨-, -, hmin⟩` from `hirr`. Set `R : H →* Matrix (Fin 2) (Fin 2) k` to `(Units.coeHom _).comp (r.comp H.subtype)`. Establish `hspan` using `GlobalTheory.BurnsideMonoid.span_matrix_eq_top_of_isAlgClosed R fun W hW => hmin W le_top fun s v hv => hW s v hv`. Set `L : Matrix (Fin 2) (Fin 2) k →ₗ[k] k` to `(Matrix.traceLinearMap (Fin 2) k k) ∘ₗ LinearMap.mulLeft k (r t : Matrix (Fin 2) (Fin 2) k)`. Establish `hL : Submodule.span k (Set.range R) ≤ LinearMap.ker L`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨h, rfl⟩`. Use `ht h h.2` as an intermediate fact. Rewrite `this` using `[map_mul, Units.val_mul]`. Conclude with `this`.

Rewrite `hL` using `[hspan]`. Establish `hz : (r t : Matrix (Fin 2) (Fin 2) k) = 0`. Use extensionality with `i j`. Establish `h` using `hL (Submodule.mem_top (x := Matrix.single j i (1 : k)))`. Establish `h2 : ((r t : Matrix (Fin 2) (Fin 2) k) * Matrix.single j i (1 : k)).trace = 0` using `h`.

Simplify `h2` using `[Matrix.trace_mul_single]`. Use `(r t).isUnit.ne_zero` as an intermediate fact. Conclude with `this hz`.
-/
private theorem coset_trace {k Γ : Type} [Field k] [IsAlgClosed k] [Group Γ] (r : Γ →* GL (Fin 2) k) (H : Subgroup Γ)
    (hirr : IsIrr (r.comp H.subtype)) (t : Γ)
    (ht : ∀ h ∈ H, (r (t * h) : Matrix (Fin 2) (Fin 2) k).trace = 0) : False := by
  obtain ⟨-, -, hmin⟩ := hirr
  let R : H →* Matrix (Fin 2) (Fin 2) k := (Units.coeHom _).comp (r.comp H.subtype)
  have hspan := GlobalTheory.BurnsideMonoid.span_matrix_eq_top_of_isAlgClosed R fun W hW => hmin W le_top fun s v hv => hW s v hv
  let L : Matrix (Fin 2) (Fin 2) k →ₗ[k] k :=
    (Matrix.traceLinearMap (Fin 2) k k) ∘ₗ LinearMap.mulLeft k (r t : Matrix (Fin 2) (Fin 2) k)
  have hL : Submodule.span k (Set.range R) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    have := ht h h.2
    rw [map_mul, Units.val_mul] at this
    exact this
  rw [hspan] at hL
  have hz : (r t : Matrix (Fin 2) (Fin 2) k) = 0 := by
    ext i j
    have h := hL (Submodule.mem_top (x := Matrix.single j i (1 : k)))
    have h2 : ((r t : Matrix (Fin 2) (Fin 2) k) * Matrix.single j i (1 : k)).trace = 0 := h
    simpa [Matrix.trace_mul_single] using h2
  have := (r t).isUnit.ne_zero
  exact this hz

/- English proof (translation)
Establish `h1 : ord ((uniformizer v : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 1`. Rewrite using `[Ad3P.DihedralUnramifiedPlaces.ord_eq v (Units.ne_zero _), valued_uniformizer, WithZero.log_exp, neg_neg]`. Establish `hord : ord (((unifUnit (Ad3.Qv v)) * (uniformizer v)⁻¹ : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 0`. Rewrite using `[ord_units_mul, ord_units_inv, h1, ord_unifUnit]`. Evaluate the numerical expressions.

Establish `h2` using `isUnramifiedChar_iff.1 h _ hord`. Rewrite `h2` using `[map_mul, map_inv, mul_inv_eq_one]`. Rewrite using `[h2, coe_localChar, HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]`.
-/
private theorem loc_val (η : HeckeCharacter ℚ) (v : Ad3.Pl) (h : IsUnramifiedChar (localChar η v)) :
    ((localChar η v (unifUnit (Ad3.Qv v)) : ℂˣ) : ℂ) = (η (IdeleClassGroup.mk ℚ (IdeleGroup.finiteEmbedding v (uniformizer v))) : ℂ) := by
  have h1 : ord ((uniformizer v : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 1 := by
    rw [Ad3P.DihedralUnramifiedPlaces.ord_eq v (Units.ne_zero _), valued_uniformizer, WithZero.log_exp, neg_neg]
  have hord : ord (((unifUnit (Ad3.Qv v)) * (uniformizer v)⁻¹ : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 0 := by
    rw [ord_units_mul, ord_units_inv, h1, ord_unifUnit]
    norm_num
  have h2 := isUnramifiedChar_iff.1 h _ hord
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h2, coe_localChar, HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]

/- English proof (translation)
Introduce and unpack `rfl`. Use `h ?_` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[coe_heckeCharacter_apply, ← coe_unitsMod, MulChar.one_apply (Units.isUnit _)]`. Both sides reduce to the same expression.
-/
private theorem hecke_ne_one {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M} (h : heckeCharacter ψ ≠ 1) : ψ ≠ 1 := by
  rintro rfl
  refine h ?_
  ext x
  rw [coe_heckeCharacter_apply, ← coe_unitsMod, MulChar.one_apply (Units.isUnit _)]
  rfl

/- English proof (translation)
Introduce and unpack `l _ Ω _ _ _ ι k N _ χ g ρ hc hirr hrep ⟨η, h1, h2, hev⟩`. Take `⟨M, _, ψ, -, rfl⟩` from `exists_heckeCharacter_eq (isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, h2⟩)`. Use `set δ : G ℚ Ω →* (Qbar l)ˣ := Chr.dirG ℚ Ω (ψ.ringHomComp ι.symm.toRingHom) with hδ`. Establish `hδc : Continuous fun s => (δ s : Qbar l)` using `dirG_cont _`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, (δ t : Qbar l) ≠ 1 := by`.

Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : (ZMod M)ˣ, ψ u ≠ 1 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Conclude with `hecke_ne_one h1 (MulChar.ext fun u => by rw [hall u, MulChar.one_apply (Units.isUnit _)])`. Take `⟨t, rfl⟩` from `(Chr.clsOnto Ω M).1 u`.

Use `⟨t, fun h => hu ?_⟩` and prove the remaining obligations. Rewrite `h` using `[dirG_val]`. Apply `ι.symm.injective` to reduce the goal to its premises. Rewrite using `[map_one]`. Conclude with `h`.

Establish `hM : ∀ᶠ w : Ad3.Pl in Filter.cofinite, ¬ normV w ∣ M` using `Filter.eventually_cofinite.2 (by simpa using fin_dvd (NeZero.ne M))`. Establish `hS` using `Filter.eventually_cofinite.1 (hrep.and (hev.and hM))`. Establish `hdense` using `GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS`. Establish `c1 : Continuous fun s : G ℚ Ω => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace * ((δ s : Qbar l) - 1)` using `(Units.continuous_val.comp hc).matrix_trace.mul (hδc.sub continuous_const)`. Establish `key : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace * ((δ s : Qbar l) - 1) = 0` using `fun s => by`.

Use `(isClosed_eq c1 continuous_const).closure_subset_iff.2 ?_ (hdense s)` and prove the remaining obligations. Introduce and unpack `σ ⟨w, hw, -, A, hA, hσ⟩`. Simplify using `only [Set.mem_setOf_eq, not_not] at hw`. Take `⟨hr, ⟨hu, hv⟩, hwM⟩` from `hw`. Establish `hAq` using `(over_iff hA _).2 dvd_rfl`.

Establish `hp` using `normV_prime w`. Take `⟨htr, -⟩` from `tr_det ι _ ((hr A hA).2 σ hσ)`. Use `show _ = (0 : Qbar l)`. Break down `hv with h0 | h0` into its components or cases. Establish `hpe : RationalSymbol.prime w = normV w`.

Rewrite using `[← absNorm_asIdeal, Ad3P.DihedralUnramifiedPlaces.normV_eq, Ad3.pOf]`. Establish `h3 : ¬ RationalSymbol.prime w ∣ M` using `by rwa [hpe]`. Establish `h4` using `(loc_val _ w hu).symm.trans (congrArg Units.val h0)`. Rewrite `h4` using `[coe_heckeCharacter_uniformizer _ h3, hpe]`. Establish `h5 : (δ σ : Qbar l) = 1`.

Rewrite using `[hδ, dirG_frob _ hp hAq hwM hσ]`. Use `show ι.symm (ψ _) = 1`. Rewrite using `[h4, Units.val_one]`. Conclude with `map_one _`. Rewrite using `[h5, sub_self, mul_zero]`.

Establish `h0' : g.a (normV w) = 0` using `by rw [Ad3P.DihedralUnramifiedPlaces.normV_eq]; exact h0`. Rewrite using `[htr, h0', map_zero, zero_mul]`. Establish `hker : IsOpen (δ.ker : Set (G ℚ Ω))` using `dirG_open _`. Use `coset_trace ρ δ.ker (hirr _ hker) t fun h hh => ?_` and prove the remaining obligations. Establish `h3` using `key (t * h)`.

Establish `h4 : (δ (t * h) : Qbar l) = δ t` using `by rw [map_mul, MonoidHom.mem_ker.1 hh, mul_one]`. Rewrite `h3` using `[h4]`. Conclude with `(mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 ht)`.
-/
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.notDih :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.NotDih := by
  rintro l _ Ω _ _ _ ι k N _ χ g ρ hc hirr hrep ⟨η, h1, h2, hev⟩
  obtain ⟨M, _, ψ, -, rfl⟩ := exists_heckeCharacter_eq (isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, h2⟩)
  set δ : G ℚ Ω →* (Qbar l)ˣ := Chr.dirG ℚ Ω (ψ.ringHomComp ι.symm.toRingHom) with hδ
  have hδc : Continuous fun s => (δ s : Qbar l) := dirG_cont _

  obtain ⟨t, ht⟩ : ∃ t, (δ t : Qbar l) ≠ 1 := by
    obtain ⟨u, hu⟩ : ∃ u : (ZMod M)ˣ, ψ u ≠ 1 := by
      by_contra hall
      push_neg at hall
      exact hecke_ne_one h1 (MulChar.ext fun u => by rw [hall u, MulChar.one_apply (Units.isUnit _)])
    obtain ⟨t, rfl⟩ := (Chr.clsOnto Ω M).1 u
    refine ⟨t, fun h => hu ?_⟩
    rw [dirG_val] at h
    apply ι.symm.injective
    rw [map_one]
    exact h

  have hM : ∀ᶠ w : Ad3.Pl in Filter.cofinite, ¬ normV w ∣ M :=
    Filter.eventually_cofinite.2 (by simpa using fin_dvd (NeZero.ne M))
  have hS := Filter.eventually_cofinite.1 (hrep.and (hev.and hM))
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have c1 : Continuous fun s : G ℚ Ω => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace * ((δ s : Qbar l) - 1) :=
    (Units.continuous_val.comp hc).matrix_trace.mul (hδc.sub continuous_const)
  have key : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace * ((δ s : Qbar l) - 1) = 0 := fun s => by
    refine (isClosed_eq c1 continuous_const).closure_subset_iff.2 ?_ (hdense s)
    rintro σ ⟨w, hw, -, A, hA, hσ⟩
    simp only [Set.mem_setOf_eq, not_not] at hw
    obtain ⟨hr, ⟨hu, hv⟩, hwM⟩ := hw
    have hAq := (over_iff hA _).2 dvd_rfl
    have hp := normV_prime w
    obtain ⟨htr, -⟩ := tr_det ι _ ((hr A hA).2 σ hσ)
    show _ = (0 : Qbar l)
    rcases hv with h0 | h0
    · have hpe : RationalSymbol.prime w = normV w := by
        rw [← absNorm_asIdeal, Ad3P.DihedralUnramifiedPlaces.normV_eq, Ad3.pOf]
      have h3 : ¬ RationalSymbol.prime w ∣ M := by rwa [hpe]
      have h4 := (loc_val _ w hu).symm.trans (congrArg Units.val h0)
      rw [coe_heckeCharacter_uniformizer _ h3, hpe] at h4
      have h5 : (δ σ : Qbar l) = 1 := by
        rw [hδ, dirG_frob _ hp hAq hwM hσ]
        show ι.symm (ψ _) = 1
        rw [h4, Units.val_one]
        exact map_one _
      rw [h5, sub_self, mul_zero]
    · have h0' : g.a (normV w) = 0 := by rw [Ad3P.DihedralUnramifiedPlaces.normV_eq]; exact h0
      rw [htr, h0', map_zero, zero_mul]
  have hker : IsOpen (δ.ker : Set (G ℚ Ω)) := dirG_open _
  refine coset_trace ρ δ.ker (hirr _ hker) t fun h hh => ?_
  have h3 := key (t * h)
  have h4 : (δ (t * h) : Qbar l) = δ t := by rw [map_mul, MonoidHom.mem_ker.1 hh, mul_one]
  rw [h4] at h3
  exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 ht)
