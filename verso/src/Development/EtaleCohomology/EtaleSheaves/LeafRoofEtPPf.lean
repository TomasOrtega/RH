import Development.EtaleCohomology.EtaleSheaves.LeafRoofEtPf

noncomputable section
open LateralTheory.E.t_E6Cut TensorProduct

namespace LateralTheory.E.LeafRoofEtPPf

/- English proof (translation)
Take `⟨e, he, hsp⟩` from `(Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg C D)).mp <| (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[D⁄C]`. Use `⟨e, he, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: e ∈ KaehlerDifferential.ideal C D` using `hsp ▸ Submodule.mem_span_singleton_self e`. Simplify `this` using `[RingHom.mem_ker]`. Establish `: x ∈ KaehlerDifferential.ideal C D` using `by simpa [RingHom.mem_ker] using hx`.

Rewrite `this` using `[hsp]`. Conclude with `this`.
-/
theorem diag {C D : Type} [CommRing C] [CommRing D] [Algebra C D] [Algebra.Etale C D] :
    ∃ e : D ⊗[C] D, IsIdempotentElem e ∧ Algebra.TensorProduct.lmul' C e = 0 ∧
      ∀ x, Algebra.TensorProduct.lmul' C x = 0 → x ∈ Ideal.span {e} := by
  obtain ⟨e, he, hsp⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg C D)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[D⁄C]
  refine ⟨e, he, ?_, fun x hx => ?_⟩
  · have : e ∈ KaehlerDifferential.ideal C D := hsp ▸ Submodule.mem_span_singleton_self e
    simpa [RingHom.mem_ker] using this
  · have : x ∈ KaehlerDifferential.ideal C D := by simpa [RingHom.mem_ker] using hx
    rw [hsp] at this
    exact this

def LeafQuotEt : Prop := ∀ (d : ℕ) {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  ((Ideal.Quotient.mk (varIdeal φ)).comp (φ.comp MvPolynomial.C)).Etale

def LeafPolyEt : Prop := ∀ (d : ℕ) {C B D : Type} [CommRing C] [CommRing B] [CommRing D] [Algebra C D]
  (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  letI := (φ.comp MvPolynomial.C).toAlgebra
  (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : D →ₐ[C] B ⊗[C] D).toRingHom
     (fun j => φ (MvPolynomial.X j) ⊗ₜ[C] (1:D))).Etale

/- English proof (translation)
Introduce `d C B _ _ φ hφ`. Use `letI : Algebra C B := (φ.comp MvPolynomial.C).toAlgebra`. Use `haveI hD : Algebra.Etale C (B ⧸ varIdeal φ) := by`. Rewrite using `[← RingHom.etale_algebraMap]`. Conclude with `h1 d φ hφ`.

Set `q : B ⊗[C] (B ⧸ varIdeal φ) →ₐ[C] (B ⧸ varIdeal φ) ⊗[C] (B ⧸ varIdeal φ)` to `Algebra.TensorProduct.map (Ideal.Quotient.mkₐ C (varIdeal φ)) (AlgHom.id C _)`. Set `m : B ⊗[C] (B ⧸ varIdeal φ) →+* B ⧸ varIdeal φ` to `((Algebra.TensorProduct.lmul' C).comp q).toRingHom`. Set `b : MvPolynomial (Fin d) (B ⧸ varIdeal φ) →+* B ⊗[C] (B ⧸ varIdeal φ)` to `MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : (B ⧸ varIdeal φ) →ₐ[C] B ⊗[C] _).toRingHom (fun j => φ (MvPolynomial.X j) ⊗ₜ[C] (1 : B ⧸ varIdeal φ))`. Take `⟨e0, hi, he0, hk0⟩` from `diag (C := C) (D := B ⧸ varIdeal φ)`. Establish `hq : Function.Surjective q` using `Algebra.TensorProduct.map_surjective _ _ (Ideal.Quotient.mkₐ_surjective C _) (fun x => ⟨x, rfl⟩)`.

Take `⟨e, rfl⟩` from `hq e0`. Establish `hbX : ∀ j, b (MvPolynomial.X j) = φ (MvPolynomial.X j) ⊗ₜ[C] (1 : B ⧸ varIdeal φ)` using `fun j => by`. Simplify using `[b]`. Establish `hker : RingHom.ker q = Ideal.span (Set.range fun j => b (MvPolynomial.X j))`. Establish `hk : RingHom.ker (Ideal.Quotient.mkₐ C (varIdeal φ)) = Ideal.span (Set.range fun j => φ (MvPolynomial.X j))`.

Use extensionality with `x`. Conclude with `Ideal.Quotient.eq_zero_iff_mem`. Rewrite using `[Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective C _), hk, Ideal.map_span, ← Set.range_comp]`. Use `congr 1`. Use extensionality with `x`.

Simplify using `[hbX]`. Establish `hmem : ∀ x, x ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) ↔ q x = 0` using `fun x => by`. Rewrite using `[← hker, RingHom.mem_ker]`. Use `⟨B ⊗[C] (B ⧸ varIdeal φ), inferInstance, algebraMap B _, b, m, e, RingHom.etale_algebraMap.mpr inferInstance, h2 d φ hφ, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`.

Rewrite using `[hbX]`. Both sides reduce to the same expression. Use extensionality with `x`. Simplify using `[m, q]`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `r`. Simplify using `[m, q, b]`. Introduce `j`. Simplify using `only [RingHom.comp_apply, hbX, MvPolynomial.constantCoeff_X]`. Simplify using `only [m, q, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one, Ideal.Quotient.mkₐ_eq_mk]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)`. Conclude with `he0`. Rewrite using `[hmem, map_sub, map_mul, hi.eq, sub_self]`. Introduce `x hx`. Take `⟨r0, hr0⟩` from `Ideal.mem_span_singleton'.mp (hk0 (q x) hx)`.

Take `⟨r, rfl⟩` from `hq r0`. Establish `: x - r * e ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j))`. Rewrite using `[hmem, map_sub, map_mul, hr0, sub_self]`. Establish `h3 : x = (x - r * e) + r * e` using `by ring`. Rewrite using `[h3]`.

Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left this) (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))`.
-/
theorem roofEtale_of_quotientEtale_polynomialEtale (h1 : LeafQuotEt) (h2 : LeafPolyEt) : LateralTheory.E.LeafRoofEtPf.LeafRoofEtP := by
  intro d C B _ _ φ hφ
  letI : Algebra C B := (φ.comp MvPolynomial.C).toAlgebra
  haveI hD : Algebra.Etale C (B ⧸ varIdeal φ) := by
    rw [← RingHom.etale_algebraMap]; exact h1 d φ hφ
  let q : B ⊗[C] (B ⧸ varIdeal φ) →ₐ[C] (B ⧸ varIdeal φ) ⊗[C] (B ⧸ varIdeal φ) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ C (varIdeal φ)) (AlgHom.id C _)
  let m : B ⊗[C] (B ⧸ varIdeal φ) →+* B ⧸ varIdeal φ := ((Algebra.TensorProduct.lmul' C).comp q).toRingHom
  let b : MvPolynomial (Fin d) (B ⧸ varIdeal φ) →+* B ⊗[C] (B ⧸ varIdeal φ) :=
    MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : (B ⧸ varIdeal φ) →ₐ[C] B ⊗[C] _).toRingHom
     (fun j => φ (MvPolynomial.X j) ⊗ₜ[C] (1 : B ⧸ varIdeal φ))
  obtain ⟨e0, hi, he0, hk0⟩ := diag (C := C) (D := B ⧸ varIdeal φ)
  have hq : Function.Surjective q :=
    Algebra.TensorProduct.map_surjective _ _ (Ideal.Quotient.mkₐ_surjective C _) (fun x => ⟨x, rfl⟩)
  obtain ⟨e, rfl⟩ := hq e0
  have hbX : ∀ j, b (MvPolynomial.X j) = φ (MvPolynomial.X j) ⊗ₜ[C] (1 : B ⧸ varIdeal φ) := fun j => by
    simp [b]
  have hker : RingHom.ker q = Ideal.span (Set.range fun j => b (MvPolynomial.X j)) := by
    have hk : RingHom.ker (Ideal.Quotient.mkₐ C (varIdeal φ)) =
        Ideal.span (Set.range fun j => φ (MvPolynomial.X j)) := by
      ext x; exact Ideal.Quotient.eq_zero_iff_mem
    rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective C _), hk, Ideal.map_span, ← Set.range_comp]
    congr 1
    ext x
    simp [hbX]
  have hmem : ∀ x, x ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) ↔ q x = 0 := fun x => by
    rw [← hker, RingHom.mem_ker]
  refine ⟨B ⊗[C] (B ⧸ varIdeal φ), inferInstance, algebraMap B _, b, m, e,
    RingHom.etale_algebraMap.mpr inferInstance, h2 d φ hφ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hbX]; rfl
  · ext x; simp [m, q]
  · apply MvPolynomial.ringHom_ext
    · intro r; simp [m, q, b]
    · intro j
      simp only [RingHom.comp_apply, hbX, MvPolynomial.constantCoeff_X]
      simp only [m, q, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one,
        Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  · exact he0
  · rw [hmem, map_sub, map_mul, hi.eq, sub_self]
  · intro x hx
    obtain ⟨r0, hr0⟩ := Ideal.mem_span_singleton'.mp (hk0 (q x) hx)
    obtain ⟨r, rfl⟩ := hq r0
    have : x - r * e ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) := by
      rw [hmem, map_sub, map_mul, hr0, sub_self]
    have h3 : x = (x - r * e) + r * e := by ring
    rw [h3]
    exact Ideal.add_mem _ (Ideal.mem_sup_left this)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))

end LateralTheory.E.LeafRoofEtPPf
