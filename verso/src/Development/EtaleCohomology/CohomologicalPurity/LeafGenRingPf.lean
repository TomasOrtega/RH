import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section

namespace LateralTheory.CohomologicalPurity.GenRingPf

open LateralTheory.CohomologicalPurity

/- English proof (translation)
Set `_` to `φ.toAlgebra`. Establish `_ : Algebra.Etale A B` using `h.1`. Set `e` to `RingEquiv.ofBijective _ h.2`. Set `f : B →ₐ[A] A ⧸ I` to `{ toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk (I.map φ)) commutes' := fun a => by`. Express the relevant statement in the definitionally equal form `e.symm (Ideal.Quotient.mk _ (φ a)) = Ideal.Quotient.mk I a`.

Rewrite using `[e.symm_apply_eq]`. Use `rfl }`. Set `g : A ⧸ I ^ 2 →ₐ[A] A ⧸ I` to `Ideal.Quotient.factorₐ A (Ideal.pow_le_self two_ne_zero)`. Establish `hg : Function.Surjective g` using `Ideal.Quotient.factor_surjective (Ideal.pow_le_self two_ne_zero)`. Establish `hn : IsNilpotent (RingHom.ker (g : A ⧸ I ^ 2 →+* A ⧸ I))`.

Use `⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot, ← le_bot_iff]`. Use `le_trans (le_of_eq (pow_two _)) ?_` and prove the remaining obligations. Use `Ideal.mul_le.mpr fun x hx z hz => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Establish `hx' : x ∈ I` using `Ideal.Quotient.eq_zero_iff_mem.mp hx`. Establish `hz' : z ∈ I` using `Ideal.Quotient.eq_zero_iff_mem.mp hz`. Rewrite using `[Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]`. Conclude with `Ideal.mul_mem_mul hx' hz'`.

Set `σ` to `Algebra.FormallySmooth.liftOfSurjective f g hg hn`. Establish `hσ : ∀ a, σ (φ a) = Ideal.Quotient.mk (I ^ 2) a` using `fun a => σ.commutes a`. Establish `hc : (σ : B →+* A ⧸ I ^ 2).comp φ = Ideal.Quotient.mk (I ^ 2)` using `RingHom.ext hσ`. Establish `h0` using `Ideal.mem_map_of_mem (σ : B →+* A ⧸ I ^ 2) hy`. Rewrite `h0` using `[Ideal.map_map, hc, Ideal.map_quotient_self, Ideal.mem_bot]`.

Express the relevant statement in the definitionally equal form `σ (φ y) = 0 at h0`. Rewrite `h0` using `[hσ]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h0`.
-/
theorem inj_sq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (h : Nbhd φ I) (y : A)
    (hy : φ y ∈ (I ^ 2).map φ) : y ∈ I ^ 2 := by
  let _ := φ.toAlgebra
  have _ : Algebra.Etale A B := h.1
  let e := RingEquiv.ofBijective _ h.2
  let f : B →ₐ[A] A ⧸ I :=
    { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk (I.map φ))
      commutes' := fun a => by
        change e.symm (Ideal.Quotient.mk _ (φ a)) = Ideal.Quotient.mk I a
        rw [e.symm_apply_eq]
        rfl }
  let g : A ⧸ I ^ 2 →ₐ[A] A ⧸ I := Ideal.Quotient.factorₐ A (Ideal.pow_le_self two_ne_zero)
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective (Ideal.pow_le_self two_ne_zero)
  have hn : IsNilpotent (RingHom.ker (g : A ⧸ I ^ 2 →+* A ⧸ I)) := by
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, ← le_bot_iff]
    refine le_trans (le_of_eq (pow_two _)) ?_
    refine Ideal.mul_le.mpr fun x hx z hz => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hx' : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
    have hz' : z ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul hx' hz'
  let σ := Algebra.FormallySmooth.liftOfSurjective f g hg hn
  have hσ : ∀ a, σ (φ a) = Ideal.Quotient.mk (I ^ 2) a := fun a => σ.commutes a
  have hc : (σ : B →+* A ⧸ I ^ 2).comp φ = Ideal.Quotient.mk (I ^ 2) := RingHom.ext hσ
  have h0 := Ideal.mem_map_of_mem (σ : B →+* A ⧸ I ^ 2) hy
  rw [Ideal.map_map, hc, Ideal.map_quotient_self, Ideal.mem_bot] at h0
  change σ (φ y) = 0 at h0
  rw [hσ] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

/- English proof (translation)
Establish `hle : Ideal.span T ≤ I.map φ` using `Ideal.span_le.mpr fun t ht => (hT t ht).1`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem t ht => exact (hT t ht).2`. Consider the case `zero => exact ⟨0, J.zero_mem, by simp⟩`.

Consider the case `add x y _ _ ihx ihy`. Take `⟨c, hc, hxc⟩` from `ihx`. Take `⟨c', hc', hyc⟩` from `ihy`. Use `⟨c + c', J.add_mem hc hc', ?_⟩` and prove the remaining obligations. Establish `: x + y - φ (c + c') = (x - φ c) + (y - φ c')` using `by rw [map_add]; ring`.

Rewrite using `[this]`. Conclude with `Ideal.add_mem _ hxc hyc`. Consider the case `smul b x hx ih`. Take `⟨c, hc, hxc⟩` from `ih`. Take `⟨c', hbc⟩` from `hs b`.

Use `⟨c' * c, J.mul_mem_left _ hc, ?_⟩` and prove the remaining obligations. Establish `: b • x - φ (c' * c) = (b - φ c') * x + φ c' * (x - φ c)`. Rewrite using `[map_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Use `Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hxc)` and prove the remaining obligations. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul hbc (hle hx)`.
-/
theorem approx {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
    (hs : ∀ b : B, ∃ c : A, b - φ c ∈ I.map φ) (J : Ideal A) (T : Set B)
    (hT : ∀ t ∈ T, t ∈ I.map φ ∧ ∃ c ∈ J, t - φ c ∈ I.map φ ^ 2) :
    ∀ z ∈ Ideal.span T, ∃ c ∈ J, z - φ c ∈ I.map φ ^ 2 := by
  have hle : Ideal.span T ≤ I.map φ := Ideal.span_le.mpr fun t ht => (hT t ht).1
  intro z hz
  induction hz using Submodule.span_induction with
  | mem t ht => exact (hT t ht).2
  | zero => exact ⟨0, J.zero_mem, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨c, hc, hxc⟩ := ihx
    obtain ⟨c', hc', hyc⟩ := ihy
    refine ⟨c + c', J.add_mem hc hc', ?_⟩
    have : x + y - φ (c + c') = (x - φ c) + (y - φ c') := by rw [map_add]; ring
    rw [this]; exact Ideal.add_mem _ hxc hyc
  | smul b x hx ih =>
    obtain ⟨c, hc, hxc⟩ := ih
    obtain ⟨c', hbc⟩ := hs b
    refine ⟨c' * c, J.mul_mem_left _ hc, ?_⟩
    have : b • x - φ (c' * c) = (b - φ c') * x + φ c' * (x - φ c) := by
      rw [map_mul, smul_eq_mul]; ring
    rw [this]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hxc)
    rw [pow_two]
    exact Ideal.mul_mem_mul hbc (hle hx)

end LateralTheory.CohomologicalPurity.GenRingPf

open LateralTheory.CohomologicalPurity.GenRingPf in
/- English proof (translation)
Introduce `d A _ I hI hC`. Take `⟨B, _, φ, ψ, hN, _, hspan, _⟩` from `hC`. Establish `hs : ∀ b : B, ∃ c : A, b - φ c ∈ I.map φ`. Introduce `b`. Take `⟨x, hx⟩` from `hN.2.2 (Ideal.Quotient.mk _ b)`.

Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[Ideal.quotientMap_mk, Ideal.Quotient.eq]`. Use `(I.map φ).neg_mem hx` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis.

Establish `hI1 : ∀ z ∈ I.map φ, ∃ c ∈ I, z - φ c ∈ I.map φ ^ 2` using `approx φ I hs I (φ '' I) (fun t ht => by`. Take `⟨i, hi, rfl⟩` from `ht`. Conclude with `⟨Ideal.mem_map_of_mem _ hi, i, hi, by simp⟩)`. Establish `hX : ∀ j, ∃ c ∈ I, ψ (MvPolynomial.X j) - φ c ∈ I.map φ ^ 2` using `fun j => hI1 _ (hspan ▸ Ideal.subset_span ⟨j, rfl⟩)`. Use `choose a ha hax using hX`.

Establish `hle : I ≤ Ideal.span (Set.range a) ⊔ I • I`. Introduce `y hy`. Establish `hy' : φ y ∈ Ideal.span (Set.range fun j => ψ (MvPolynomial.X j))` using `hspan ▸ Ideal.mem_map_of_mem _ hy`. Take `⟨c, hc, hyc⟩` from `approx φ I hs (Ideal.span (Set.range a)) _ (fun t ht => by`. Take `⟨j, rfl⟩` from `ht`.

Conclude with `⟨hspan ▸ Ideal.subset_span ⟨j, rfl⟩, a j, Ideal.subset_span ⟨j, rfl⟩, hax j⟩) _ hy'`. Establish `h2 : y - c ∈ I ^ 2` using `inj_sq φ I hN _ (by rw [map_sub, Ideal.map_pow]; exact hyc)`. Establish `: y = c + (y - c)` using `by ring`. Rewrite using `[this]`. Use `Submodule.add_mem_sup hc ?_` and prove the remaining obligations.

Rewrite using `[Ideal.smul_eq_mul, ← pow_two]`. Conclude with `h2`. Take `⟨r, hr, hrle⟩` from `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hI le_rfl hle`. Use `⟨a, r, hr, ha, fun y hy => ?_⟩` and prove the remaining obligations. Use `hrle (Submodule.smul_mem_pointwise_smul y r I hy)` as an intermediate fact.

Simplify `this` using `[smul_eq_mul]`.
-/
theorem LateralTheory.CohomologicalPurity.Cl.LeafGenRing_of : LateralTheory.CohomologicalPurity.Cl.LeafGenRing := by
  intro d A _ I hI hC
  obtain ⟨B, _, φ, ψ, hN, _, hspan, _⟩ := hC
  have hs : ∀ b : B, ∃ c : A, b - φ c ∈ I.map φ := by
    intro b
    obtain ⟨x, hx⟩ := hN.2.2 (Ideal.Quotient.mk _ b)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨c, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
    have := (I.map φ).neg_mem hx
    rwa [neg_sub] at this
  have hI1 : ∀ z ∈ I.map φ, ∃ c ∈ I, z - φ c ∈ I.map φ ^ 2 :=
    approx φ I hs I (φ '' I) (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := ht
      exact ⟨Ideal.mem_map_of_mem _ hi, i, hi, by simp⟩)
  have hX : ∀ j, ∃ c ∈ I, ψ (MvPolynomial.X j) - φ c ∈ I.map φ ^ 2 := fun j =>
    hI1 _ (hspan ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose a ha hax using hX
  have hle : I ≤ Ideal.span (Set.range a) ⊔ I • I := by
    intro y hy
    have hy' : φ y ∈ Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) := hspan ▸ Ideal.mem_map_of_mem _ hy
    obtain ⟨c, hc, hyc⟩ := approx φ I hs (Ideal.span (Set.range a)) _ (fun t ht => by
      obtain ⟨j, rfl⟩ := ht
      exact ⟨hspan ▸ Ideal.subset_span ⟨j, rfl⟩, a j, Ideal.subset_span ⟨j, rfl⟩, hax j⟩) _ hy'
    have h2 : y - c ∈ I ^ 2 := inj_sq φ I hN _ (by rw [map_sub, Ideal.map_pow]; exact hyc)
    have : y = c + (y - c) := by ring
    rw [this]
    refine Submodule.add_mem_sup hc ?_
    rw [Ideal.smul_eq_mul, ← pow_two]; exact h2
  obtain ⟨r, hr, hrle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hI le_rfl hle
  refine ⟨a, r, hr, ha, fun y hy => ?_⟩
  have := hrle (Submodule.smul_mem_pointwise_smul y r I hy)
  simpa [smul_eq_mul] using this
