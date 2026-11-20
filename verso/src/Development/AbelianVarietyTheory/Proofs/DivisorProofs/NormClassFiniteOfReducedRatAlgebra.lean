import Mathlib
open scoped TensorProduct Classical

namespace GlobalTheory
namespace ReducedInvolutionNormClass

variable {E : Type} [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]

/- English proof (translation)
Use `letI := Ideal.Quotient.field I`. Establish `hfin : Module.Finite ℚ (E ⧸ I)` using `Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ I).toLinearMap Ideal.Quotient.mk_surjective`. Use `haveI : CharZero (E ⧸ I) := charZero_of_injective_ringHom (algebraMap ℚ (E ⧸ I)).injective`. Conclude with `@NumberField.mk _ _ _ (by`. Use `hfin` and compare the differences between its conclusion and the goal.

Conclude with `congrArg (fun A : Algebra ℚ (E ⧸ I) => A.toModule) (Subsingleton.elim _ (Ideal.Quotient.algebra ℚ)))`.
-/
theorem numberField_quot (I : Ideal E) [I.IsMaximal] :
    @NumberField (E ⧸ I) (Ideal.Quotient.field I) := by
  letI := Ideal.Quotient.field I
  have hfin : Module.Finite ℚ (E ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : CharZero (E ⧸ I) := charZero_of_injective_ringHom (algebraMap ℚ (E ⧸ I)).injective
  exact @NumberField.mk _ _ _ (by
    convert hfin
    exact congrArg (fun A : Algebra ℚ (E ⧸ I) => A.toModule) (Subsingleton.elim _ (Ideal.Quotient.algebra ℚ)))

/- English proof (translation)
Use `letI := Ideal.Quotient.field I`. Use `haveI := numberField_quot I`. Establish `hmap : I = I.map (τ : E ≃+* E)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`.

Establish `: x = (τ : E ≃+* E) (τ x)` using `(hτ x).symm`. Rewrite using `[this]`. Conclude with `Ideal.mem_map_of_mem _ (hI x hx)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`.

Conclude with `hI x hx`. Set `τI` to `Ideal.quotientEquiv I I (τ : E ≃+* E) hmap`. Establish `hτmk : ∀ x, τI (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (τ x)` using `fun x => rfl`. Establish `hτI : ∀ z, τI (τI z) = z`. Introduce `z`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Rewrite using `[hτmk, hτmk, hτ]`. Take `⟨M, hM⟩` from `H (E ⧸ I) τI hτI S`. Set `lift : E ⧸ I → E` to `fun z => Classical.choose (Ideal.Quotient.mk_surjective z)`. Establish `hlift : ∀ z, Ideal.Quotient.mk I (lift z) = z` using `fun z => Classical.choose_spec (Ideal.Quotient.mk_surjective z)`.

Use `⟨M.image lift, fun a ha hτa hyp => ?_⟩` and prove the remaining obligations. Establish `ha0 : Ideal.Quotient.mk I a ≠ 0` using `(ha.map _).ne_zero`. Take `⟨m, hm, e', he', hae⟩` from `hM (Ideal.Quotient.mk I a) ha0 (by rw [hτmk, hτa]) (by`. Introduce `ℓ hℓ hS`. Take `⟨b, x, y, hb, h1, h2, d, hd, hx, hy⟩` from `hyp ℓ hℓ hS`.

Use `⟨Ideal.Quotient.mk I b, Ideal.Quotient.mk I x, Ideal.Quotient.mk I y, (hb.map _).ne_zero, ?_, ?_, d, hd, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hτmk, h1, map_mul, map_mul]`. Rewrite using `[hτmk, ← map_mul, h2, map_mul]`. Use `hx.map (Ideal.Quotient.mk I).toIntAlgHom` as an intermediate fact. Simplify using `only [map_mul, map_natCast, RingHom.toIntAlgHom_apply] at this`.

Use `this using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first | rfl | exact Subsingleton.elim _ _ | (congr; exact Subsingleton.elim _ _)`. Use `hy.map (Ideal.Quotient.mk I).toIntAlgHom` as an intermediate fact. Simplify using `only [map_mul, map_natCast, RingHom.toIntAlgHom_apply] at this`. Use `this using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `all_goals first | rfl | exact Subsingleton.elim _ _ | (congr; exact Subsingleton.elim _ _))`. Take `⟨e, rfl⟩` from `Ideal.Quotient.mk_surjective e'`. Use `⟨lift m, Finset.mem_image_of_mem _ hm, e, ?_, ?_⟩` and prove the remaining obligations. Introduce `he`. Conclude with `he' (Ideal.Quotient.eq_zero_iff_mem.2 he)`.

Rewrite using `[← Ideal.Quotient.eq, map_mul, map_mul, hlift, hae, hτmk]`.
-/
theorem stable_factor (H : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e)) (τ : E ≃ₐ[ℚ] E) (hτ : ∀ x, τ (τ x) = x) (S : Finset ℕ)
    (I : Ideal E) [I.IsMaximal] (hI : ∀ x ∈ I, τ x ∈ I) :
    ∃ M : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ m ∈ M, ∃ e : E, e ∉ I ∧ a - e * m * τ e ∈ I := by
  letI := Ideal.Quotient.field I
  haveI := numberField_quot I
  have hmap : I = I.map (τ : E ≃+* E) := by
    apply le_antisymm
    · intro x hx
      have : x = (τ : E ≃+* E) (τ x) := (hτ x).symm
      rw [this]; exact Ideal.mem_map_of_mem _ (hI x hx)
    · rw [Ideal.map_le_iff_le_comap]; intro x hx; exact hI x hx
  let τI := Ideal.quotientEquiv I I (τ : E ≃+* E) hmap
  have hτmk : ∀ x, τI (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (τ x) := fun x => rfl
  have hτI : ∀ z, τI (τI z) = z := by
    intro z; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hτmk, hτmk, hτ]
  obtain ⟨M, hM⟩ := H (E ⧸ I) τI hτI S
  let lift : E ⧸ I → E := fun z => Classical.choose (Ideal.Quotient.mk_surjective z)
  have hlift : ∀ z, Ideal.Quotient.mk I (lift z) = z :=
    fun z => Classical.choose_spec (Ideal.Quotient.mk_surjective z)
  refine ⟨M.image lift, fun a ha hτa hyp => ?_⟩
  have ha0 : Ideal.Quotient.mk I a ≠ 0 := (ha.map _).ne_zero
  obtain ⟨m, hm, e', he', hae⟩ := hM (Ideal.Quotient.mk I a) ha0 (by rw [hτmk, hτa]) (by
    intro ℓ hℓ hS
    obtain ⟨b, x, y, hb, h1, h2, d, hd, hx, hy⟩ := hyp ℓ hℓ hS
    refine ⟨Ideal.Quotient.mk I b, Ideal.Quotient.mk I x, Ideal.Quotient.mk I y,
      (hb.map _).ne_zero, ?_, ?_, d, hd, ?_, ?_⟩
    · rw [hτmk, h1, map_mul, map_mul]
    · rw [hτmk, ← map_mul, h2, map_mul]
    · have := hx.map (Ideal.Quotient.mk I).toIntAlgHom
      simp only [map_mul, map_natCast, RingHom.toIntAlgHom_apply] at this
      convert this using 1
      all_goals first | rfl | exact Subsingleton.elim _ _ | (congr; exact Subsingleton.elim _ _)
    · have := hy.map (Ideal.Quotient.mk I).toIntAlgHom
      simp only [map_mul, map_natCast, RingHom.toIntAlgHom_apply] at this
      convert this using 1
      all_goals first | rfl | exact Subsingleton.elim _ _ | (congr; exact Subsingleton.elim _ _))
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e'
  refine ⟨lift m, Finset.mem_image_of_mem _ hm, e, ?_, ?_⟩
  · intro he; exact he' (Ideal.Quotient.eq_zero_iff_mem.2 he)
  · rw [← Ideal.Quotient.eq, map_mul, map_mul, hlift, hae, hτmk]

variable [IsReduced E]

/- English proof (translation)
Use `haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E`. Use `⟨(IsArtinianRing.equivPi E).symm (fun I => Ideal.Quotient.mk I.asIdeal (c I)), fun I => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `congrFun ((IsArtinianRing.equivPi E).apply_symm_apply (fun I => Ideal.Quotient.mk I.asIdeal (c I))) I`.
-/
theorem crt (c : MaximalSpectrum E → E) : ∃ u : E, ∀ I : MaximalSpectrum E, u - c I ∈ I.asIdeal := by
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  refine ⟨(IsArtinianRing.equivPi E).symm (fun I => Ideal.Quotient.mk I.asIdeal (c I)), fun I => ?_⟩
  rw [← Ideal.Quotient.eq]
  exact congrFun ((IsArtinianRing.equivPi E).apply_symm_apply
    (fun I => Ideal.Quotient.mk I.asIdeal (c I))) I

/- English proof (translation)
Use `haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E`. Apply `(IsArtinianRing.equivPi E).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use function extensionality and compare the values at `I`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (h I)`.
-/
theorem eq_zero_of_mem_all (x : E) (h : ∀ I : MaximalSpectrum E, x ∈ I.asIdeal) : x = 0 := by
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  apply (IsArtinianRing.equivPi E).injective
  rw [map_zero]; funext I; exact Ideal.Quotient.eq_zero_iff_mem.2 (h I)

end ReducedInvolutionNormClass

open ReducedInvolutionNormClass in

/- English proof (translation)
Introduce `H E _ _ _ _ τ hτ S`. Use `haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E`. Use `haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _`. Set `σ : MaximalSpectrum E → MaximalSpectrum E` to `fun I => ⟨I.asIdeal.comap (τ : E ≃+* E), Ideal.comap_isMaximal_of_surjective _ (τ : E ≃+* E).surjective⟩`. Establish `hσ : ∀ I x, x ∈ (σ I).asIdeal ↔ τ x ∈ I.asIdeal` using `fun I x => Iff.rfl`.

Establish `hσσ : ∀ I, σ (σ I) = I` using `fun I => MaximalSpectrum.ext (Ideal.ext fun x => by rw [hσ, hσ, hτ])`. Establish `hst : ∀ I, σ I = I → ∀ x ∈ I.asIdeal, τ x ∈ I.asIdeal`. Introduce `I h x hx`. Rewrite using `[← hσ, h]`. Conclude with `hx`.

Set `n` to `Fintype.equivFin (MaximalSpectrum E)`. Set `ch : MaximalSpectrum E → Prop` to `fun I => n I < n (σ I)`. Set `Mset : MaximalSpectrum E → Finset E` to `fun I => if h : σ I = I then Classical.choose (stable_factor H τ hτ S I.asIdeal (hst I h)) else {1}`. Set `F : (MaximalSpectrum E → E) → E` to `fun f => Classical.choose (crt f)`. Establish `hF : ∀ f I, F f - f I ∈ I.asIdeal` using `fun f => Classical.choose_spec (crt f)`.

Use `⟨(Fintype.piFinset Mset).image F, fun a ha hτa hyp => ?_⟩` and prove the remaining obligations. Establish `key : ∀ I, ∃ m ∈ Mset I, ∃ e : E, e ∉ I.asIdeal ∧ (σ I = I → a - e * m * τ e ∈ I.asIdeal) ∧ (σ I ≠ I → m = 1 ∧ e = if ch I then a else 1)`. Introduce `I`. Distinguish the cases in `h : σ I = I`. Take `⟨m, hm, e, he, hae⟩` from `Classical.choose_spec (stable_factor H τ hτ S I.asIdeal (hst I h)) a ha hτa hyp`.

Use `⟨m, by simp only [Mset, dif_pos h]; exact hm, e, he, fun _ => hae, fun h' => absurd h h'⟩` and prove the remaining obligations. Use `⟨1, by simp [Mset, h], if ch I then a else 1, ?_, fun h' => absurd h' h, fun _ => ⟨rfl, rfl⟩⟩ split_ifs` and prove the remaining obligations. Conclude with `fun hmem => I.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ha)`. Conclude with `fun hmem => I.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 hmem)`. Use `choose m hm e he hst1 hst2 using key`.

Take `⟨u, hu⟩` from `crt e`. Establish `hunit : IsUnit u`. Assume the negation of the conclusion as `hn`. Take `⟨J, hJ, huJ⟩` from `exists_max_ideal_of_mem_nonunits hn`. Apply `he ⟨J, hJ⟩` to reduce the goal to its premises.

Use `J.sub_mem huJ (hu ⟨J, hJ⟩)` as an intermediate fact. Simplify using `using this`. Use `⟨F m, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hm), hunit.unit, ?_⟩` and prove the remaining obligations. Simplify using `only [IsUnit.unit_spec]`. Rewrite using `[← sub_eq_zero]`.

Apply `eq_zero_of_mem_all` to reduce the goal to its premises. Introduce `I`. Establish `hu' : ∀ J : MaximalSpectrum E, Ideal.Quotient.mk J.asIdeal u = Ideal.Quotient.mk J.asIdeal (e J)` using `fun J => Ideal.Quotient.eq.2 (hu J)`. Establish `hF' : Ideal.Quotient.mk I.asIdeal (F m) = Ideal.Quotient.mk I.asIdeal (m I)` using `Ideal.Quotient.eq.2 (hF m I)`. Establish `hτu : ∀ J, Ideal.Quotient.mk J.asIdeal (τ u) = Ideal.Quotient.mk J.asIdeal (τ (e (σ J)))`.

Introduce `J`. Rewrite using `[Ideal.Quotient.eq, ← map_sub, ← hσ]`. Conclude with `hu (σ J)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hu', hF', hτu, sub_eq_zero]`. Distinguish the cases in `h : σ I = I`.

Rewrite using `[h, ← map_mul, ← map_mul, Ideal.Quotient.eq]`. Conclude with `hst1 I h`. Take `⟨hm1, he1⟩` from `hst2 I h`. Establish `hJ : σ (σ I) ≠ σ I` using `by rw [hσσ]; exact fun h' => h h'.symm`. Take `⟨_, he2⟩` from `hst2 (σ I) hJ`.

Rewrite using `[hm1, he1, he2]`. Establish `hne : n I ≠ n (σ I)` using `fun h' => h (n.injective h').symm`. Distinguish the cases in `hc : ch I`. Establish `hc' : ¬ ch (σ I)` using `by show ¬ n (σ I) < n (σ (σ I)); rw [hσσ]; exact not_lt.2 hc.le`. Rewrite using `[if_pos hc, if_neg hc']`.

Simplify using the standard rewrite rules. Establish `hc' : ch (σ I)` using `by show n (σ I) < n (σ (σ I)); rw [hσσ]; exact lt_of_le_of_ne (not_lt.1 hc) hne.symm`. Rewrite using `[if_neg hc, if_pos hc', hτa]`. Simplify using the standard rewrite rules.
-/
theorem normClassFinite_of_reduced : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e) →
  ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e := by
  intro H E _ _ _ _ τ hτ S
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  let σ : MaximalSpectrum E → MaximalSpectrum E := fun I =>
    ⟨I.asIdeal.comap (τ : E ≃+* E), Ideal.comap_isMaximal_of_surjective _ (τ : E ≃+* E).surjective⟩
  have hσ : ∀ I x, x ∈ (σ I).asIdeal ↔ τ x ∈ I.asIdeal := fun I x => Iff.rfl
  have hσσ : ∀ I, σ (σ I) = I := fun I =>
    MaximalSpectrum.ext (Ideal.ext fun x => by rw [hσ, hσ, hτ])
  have hst : ∀ I, σ I = I → ∀ x ∈ I.asIdeal, τ x ∈ I.asIdeal := by
    intro I h x hx; rw [← hσ, h]; exact hx
  let n := Fintype.equivFin (MaximalSpectrum E)
  let ch : MaximalSpectrum E → Prop := fun I => n I < n (σ I)
  let Mset : MaximalSpectrum E → Finset E := fun I =>
    if h : σ I = I then Classical.choose (stable_factor H τ hτ S I.asIdeal (hst I h)) else {1}
  let F : (MaximalSpectrum E → E) → E := fun f => Classical.choose (crt f)
  have hF : ∀ f I, F f - f I ∈ I.asIdeal := fun f => Classical.choose_spec (crt f)
  refine ⟨(Fintype.piFinset Mset).image F, fun a ha hτa hyp => ?_⟩
  have key : ∀ I, ∃ m ∈ Mset I, ∃ e : E, e ∉ I.asIdeal ∧ (σ I = I → a - e * m * τ e ∈ I.asIdeal) ∧
      (σ I ≠ I → m = 1 ∧ e = if ch I then a else 1) := by
    intro I
    by_cases h : σ I = I
    · obtain ⟨m, hm, e, he, hae⟩ :=
        Classical.choose_spec (stable_factor H τ hτ S I.asIdeal (hst I h)) a ha hτa hyp
      refine ⟨m, by simp only [Mset, dif_pos h]; exact hm, e, he, fun _ => hae, fun h' => absurd h h'⟩
    · refine ⟨1, by simp [Mset, h], if ch I then a else 1, ?_, fun h' => absurd h' h, fun _ => ⟨rfl, rfl⟩⟩
      split_ifs
      · exact fun hmem => I.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ha)
      · exact fun hmem => I.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 hmem)
  choose m hm e he hst1 hst2 using key
  obtain ⟨u, hu⟩ := crt e
  have hunit : IsUnit u := by
    by_contra hn
    obtain ⟨J, hJ, huJ⟩ := exists_max_ideal_of_mem_nonunits hn
    apply he ⟨J, hJ⟩
    have := J.sub_mem huJ (hu ⟨J, hJ⟩)
    simpa using this
  refine ⟨F m, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hm), hunit.unit, ?_⟩
  simp only [IsUnit.unit_spec]
  rw [← sub_eq_zero]
  apply eq_zero_of_mem_all
  intro I
  have hu' : ∀ J : MaximalSpectrum E, Ideal.Quotient.mk J.asIdeal u = Ideal.Quotient.mk J.asIdeal (e J) :=
    fun J => Ideal.Quotient.eq.2 (hu J)
  have hF' : Ideal.Quotient.mk I.asIdeal (F m) = Ideal.Quotient.mk I.asIdeal (m I) :=
    Ideal.Quotient.eq.2 (hF m I)
  have hτu : ∀ J, Ideal.Quotient.mk J.asIdeal (τ u) = Ideal.Quotient.mk J.asIdeal (τ (e (σ J))) := by
    intro J; rw [Ideal.Quotient.eq, ← map_sub, ← hσ]; exact hu (σ J)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hu', hF', hτu, sub_eq_zero]
  by_cases h : σ I = I
  · rw [h, ← map_mul, ← map_mul, Ideal.Quotient.eq]
    exact hst1 I h
  · obtain ⟨hm1, he1⟩ := hst2 I h
    have hJ : σ (σ I) ≠ σ I := by rw [hσσ]; exact fun h' => h h'.symm
    obtain ⟨_, he2⟩ := hst2 (σ I) hJ
    rw [hm1, he1, he2]
    have hne : n I ≠ n (σ I) := fun h' => h (n.injective h').symm
    by_cases hc : ch I
    · have hc' : ¬ ch (σ I) := by
        show ¬ n (σ I) < n (σ (σ I)); rw [hσσ]; exact not_lt.2 hc.le
      rw [if_pos hc, if_neg hc']
      simp
    · have hc' : ch (σ I) := by
        show n (σ I) < n (σ (σ I)); rw [hσσ]; exact lt_of_le_of_ne (not_lt.1 hc) hne.symm
      rw [if_neg hc, if_pos hc', hτa]
      simp

end GlobalTheory
