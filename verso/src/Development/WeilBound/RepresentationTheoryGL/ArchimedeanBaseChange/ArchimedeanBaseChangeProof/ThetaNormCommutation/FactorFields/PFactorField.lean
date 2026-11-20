import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FactorFieldP

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev cj (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

/- English proof (translation)
Use extensionality with `x`. Conclude with `IsCMField.complexEmbedding_complexConj E φ x`.
-/
theorem emb_cj (φ : E →+* ℂ) : φ.comp (cj E) = (starRingEnd ℂ).comp φ := by
  ext x
  exact IsCMField.complexEmbedding_complexConj E φ x

/- English proof (translation)
Rewrite using `[Complex.inv_def, Complex.normSq_eq_norm_sq, h]`. Simplify using the standard rewrite rules.
-/
theorem conj_eq_inv {z : ℂ} (h : ‖z‖ = 1) : (starRingEnd ℂ) z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

abbrev Good (Q : E[X]) : Prop := ∀ τ : E →+* ℂ, ∀ z ∈ (Q.map τ).roots, ‖z‖ = 1

variable (Q : E[X]) [Fact (Irreducible Q)]

instance finL : Module.Finite E (AdjoinRoot Q) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finite

instance nfL : NumberField (AdjoinRoot Q) := NumberField.of_module_finite E (AdjoinRoot Q)

/- English proof (translation)
Apply `h (ψ.comp (AdjoinRoot.of Q))` to reduce the goal to its premises. Rewrite using `[Polynomial.mem_roots (Polynomial.map_ne_zero (Fact.out : Irreducible Q).ne_zero), Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]`.
-/
theorem root_norm (h : Good Q) (ψ : AdjoinRoot Q →+* ℂ) : ‖ψ (AdjoinRoot.root Q)‖ = 1 := by
  apply h (ψ.comp (AdjoinRoot.of Q))
  rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Fact.out : Irreducible Q).ne_zero), Polynomial.IsRoot,
    Polynomial.eval_map, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

/- English proof (translation)
Set `ψ : AdjoinRoot Q →+* ℂ` to `Classical.choice (inferInstance : Nonempty _)`. Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[Polynomial.hom_eval₂, map_zero, map_inv₀, ← conj_eq_inv (root_norm Q h ψ), ← RingHom.comp_assoc, emb_cj, ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero, map_zero]`.
-/
theorem csr (h : Good Q) :
    Polynomial.eval₂ ((AdjoinRoot.of Q).comp (cj E)) (AdjoinRoot.root Q)⁻¹ Q = 0 := by
  let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply ψ.injective
  rw [Polynomial.hom_eval₂, map_zero, map_inv₀, ← conj_eq_inv (root_norm Q h ψ), ← RingHom.comp_assoc, emb_cj,
    ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero, map_zero]

def sig (h : Good Q) : AdjoinRoot Q →+* AdjoinRoot Q :=
  AdjoinRoot.lift ((AdjoinRoot.of Q).comp (cj E)) (AdjoinRoot.root Q)⁻¹ (csr Q h)

/- English proof (translation)
Unfold `sig`. Use `erw [AdjoinRoot.lift_of]`. Both sides reduce to the same expression.
-/
theorem sig_of (h : Good Q) (x : E) : sig Q h (AdjoinRoot.of Q x) = AdjoinRoot.of Q (IsCMField.complexConj E x) := by
  unfold sig
  erw [AdjoinRoot.lift_of]
  rfl

/- English proof (translation)
Unfold `sig`. Conclude with `AdjoinRoot.lift_root _`.
-/
theorem sig_root (h : Good Q) : sig Q h (AdjoinRoot.root Q) = (AdjoinRoot.root Q)⁻¹ := by
  unfold sig
  exact AdjoinRoot.lift_root _

/- English proof (translation)
Establish `e : ψ.comp (sig Q h) = (starRingEnd ℂ).comp ψ`. Apply `AdjoinRoot.ringHom_ext` to reduce the goal to its premises. Use extensionality with `y`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, sig_of]`. Conclude with `IsCMField.complexEmbedding_complexConj E (ψ.comp (AdjoinRoot.of Q)) y`.

Simplify using `only [RingHom.coe_comp, Function.comp_apply, sig_root, map_inv₀]`. Rewrite using `[conj_eq_inv (root_norm Q h ψ)]`. Conclude with `RingHom.congr_fun e x`.
-/
theorem emb_sig (h : Good Q) (ψ : AdjoinRoot Q →+* ℂ) (x : AdjoinRoot Q) :
    ψ (sig Q h x) = starRingEnd ℂ (ψ x) := by
  have e : ψ.comp (sig Q h) = (starRingEnd ℂ).comp ψ := by
    apply AdjoinRoot.ringHom_ext
    · ext y
      simp only [RingHom.coe_comp, Function.comp_apply, sig_of]
      exact IsCMField.complexEmbedding_complexConj E (ψ.comp (AdjoinRoot.of Q)) y
    · simp only [RingHom.coe_comp, Function.comp_apply, sig_root, map_inv₀]
      rw [conj_eq_inv (root_norm Q h ψ)]
  exact RingHom.congr_fun e x

/- English proof (translation)
Set `ψ : AdjoinRoot Q →+* ℂ` to `Classical.choice (inferInstance : Nonempty _)`. Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[emb_sig, emb_sig, Complex.conj_conj]`.
-/
theorem sig_sig (h : Good Q) (x : AdjoinRoot Q) : sig Q h (sig Q h x) = x := by
  let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply ψ.injective
  rw [emb_sig, emb_sig, Complex.conj_conj]

/- English proof (translation)
Use `show sig Q h (AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)) = AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)`. Rewrite using `[sig_of]`. Use `congr 1`. Conclude with `(IsCMField.complexConj E).commutes x`.
-/
theorem sig_alg (h : Good Q) (x : maximalRealSubfield E) :
    sig Q h (algebraMap (maximalRealSubfield E) (AdjoinRoot Q) x) =
      algebraMap (maximalRealSubfield E) (AdjoinRoot Q) x := by
  show sig Q h (AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)) =
    AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)
  rw [sig_of]
  congr 1
  exact (IsCMField.complexConj E).commutes x

def Kf (h : Good Q) : IntermediateField (maximalRealSubfield E) (AdjoinRoot Q) :=
  (RingHom.eqLocusField (sig Q h) (RingHom.id _)).toIntermediateField fun x => sig_alg Q h x

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Kf (h : Good Q) {x : AdjoinRoot Q} : x ∈ Kf Q h ↔ sig Q h x = x := Iff.rfl

/- English proof (translation)
Use `⟨fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`. Use `letI : Algebra (Kf Q h) ℂ := w.embedding.toAlgebra`. Set `ψ : AdjoinRoot Q →ₐ[Kf Q h] ℂ` to `IsAlgClosed.lift`. Use extensionality with `x`.

Establish `hx : w.embedding x = ψ.toRingHom (x : AdjoinRoot Q)` using `(ψ.commutes x).symm`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, hx, ← emb_sig Q h ψ.toRingHom, (mem_Kf Q h).1 x.2]`.
-/
theorem totReal (h : Good Q) : IsTotallyReal (Kf Q h) := by
  refine ⟨fun w => ?_⟩
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  letI : Algebra (Kf Q h) ℂ := w.embedding.toAlgebra
  let ψ : AdjoinRoot Q →ₐ[Kf Q h] ℂ := IsAlgClosed.lift
  ext x
  have hx : w.embedding x = ψ.toRingHom (x : AdjoinRoot Q) := (ψ.commutes x).symm
  rw [ComplexEmbedding.conjugate_coe_eq, hx, ← emb_sig Q h ψ.toRingHom, (mem_Kf Q h).1 x.2]

/- English proof (translation)
Establish `h2 : (2 : AdjoinRoot Q) ≠ 0` using `two_ne_zero`. Use `⟨⟨(z + sig Q h z) / 2, ?_⟩, ⟨(z - sig Q h z) / (2 * S), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_Kf, map_div₀, map_add, sig_sig, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mem_Kf, map_div₀, map_sub, map_mul, sig_sig, map_ofNat, hσS]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `show z = (z + sig Q h z) / 2 + S * ((z - sig Q h z) / (2 * S))`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem decomp (h : Good Q) {S : AdjoinRoot Q} (hS : S ≠ 0) (hσS : sig Q h S = -S) (z : AdjoinRoot Q) :
    ∃ a b : Kf Q h, z = (a : AdjoinRoot Q) + S * (b : AdjoinRoot Q) := by
  have h2 : (2 : AdjoinRoot Q) ≠ 0 := two_ne_zero
  refine ⟨⟨(z + sig Q h z) / 2, ?_⟩, ⟨(z - sig Q h z) / (2 * S), ?_⟩, ?_⟩
  · rw [mem_Kf, map_div₀, map_add, sig_sig, map_ofNat]
    ring
  · rw [mem_Kf, map_div₀, map_sub, map_mul, sig_sig, map_ofNat, hσS]
    field_simp
    ring
  · show z = (z + sig Q h z) / 2 + S * ((z - sig Q h z) / (2 * S))
    field_simp
    ring

/- English proof (translation)
Establish `hS : AdjoinRoot.of Q s ≠ 0` using `(_root_.map_ne_zero _).2 hs`. Establish `hσS : sig Q h (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s`. Rewrite using `[sig_of, hsc, map_neg]`. Establish `hle : Module.finrank (Kf Q h) (AdjoinRoot Q) ≤ 2`. Establish `hspan : Submodule.span (Kf Q h) (Set.range ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]) = ⊤`.

Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations. Take `⟨a, b, hz⟩` from `decomp Q h hS hσS z`. Establish `e : z = a • (1 : AdjoinRoot Q) + b • AdjoinRoot.of Q s`. Rewrite using `[hz, Algebra.smul_def, Algebra.smul_def, mul_one]`. Conclude with `congrArg (fun t => (a : AdjoinRoot Q) + t) (mul_comm _ _)`.

Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ a (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.smul_mem _ b (Submodule.subset_span ⟨1, rfl⟩))`. Use `finrank_range_le_card (R := Kf Q h) ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]` as an intermediate fact. Rewrite `this` using `[Set.finrank, hspan, finrank_top, Fintype.card_fin]`. Conclude with `this`.

Establish `hne1 : Module.finrank (Kf Q h) (AdjoinRoot Q) ≠ 1`. Introduce `h1`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (1 : AdjoinRoot Q) one_ne_zero).1 h1 (AdjoinRoot.of Q s)`. Rewrite `hc` using `[Algebra.smul_def, mul_one]`. Establish `hm : AdjoinRoot.of Q s ∈ Kf Q h` using `hc ▸ c.2`.

Rewrite `hm` using `[mem_Kf, hσS]`. Establish `h2 : (2 : AdjoinRoot Q) * AdjoinRoot.of Q s = 0` using `by linear_combination (-1 : AdjoinRoot Q) * hm`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `two_ne_zero h3`. Conclude with `hS h3`.

Establish `hpos : 0 < Module.finrank (Kf Q h) (AdjoinRoot Q)` using `Module.finrank_pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_KL (h : Good Q) {s : E} (hs : s ≠ 0) (hsc : IsCMField.complexConj E s = -s) :
    Module.finrank (Kf Q h) (AdjoinRoot Q) = 2 := by
  have hS : AdjoinRoot.of Q s ≠ 0 := (_root_.map_ne_zero _).2 hs
  have hσS : sig Q h (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s := by
    rw [sig_of, hsc, map_neg]
  have hle : Module.finrank (Kf Q h) (AdjoinRoot Q) ≤ 2 := by
    have hspan : Submodule.span (Kf Q h) (Set.range ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]) = ⊤ := by
      refine eq_top_iff.2 fun z _ => ?_
      obtain ⟨a, b, hz⟩ := decomp Q h hS hσS z
      have e : z = a • (1 : AdjoinRoot Q) + b • AdjoinRoot.of Q s := by
        rw [hz, Algebra.smul_def, Algebra.smul_def, mul_one]
        exact congrArg (fun t => (a : AdjoinRoot Q) + t) (mul_comm _ _)
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ a (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ b (Submodule.subset_span ⟨1, rfl⟩))
    have := finrank_range_le_card (R := Kf Q h) ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]
    rw [Set.finrank, hspan, finrank_top, Fintype.card_fin] at this
    exact this
  have hne1 : Module.finrank (Kf Q h) (AdjoinRoot Q) ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : AdjoinRoot Q) one_ne_zero).1 h1 (AdjoinRoot.of Q s)
    rw [Algebra.smul_def, mul_one] at hc
    have hm : AdjoinRoot.of Q s ∈ Kf Q h := hc ▸ c.2
    rw [mem_Kf, hσS] at hm
    have h2 : (2 : AdjoinRoot Q) * AdjoinRoot.of Q s = 0 := by linear_combination (-1 : AdjoinRoot Q) * hm
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact two_ne_zero h3
    · exact hS h3
  have hpos : 0 < Module.finrank (Kf Q h) (AdjoinRoot Q) := Module.finrank_pos
  omega

/- English proof (translation)
Establish `h1` using `Module.finrank_mul_finrank (maximalRealSubfield E) E (AdjoinRoot Q)`. Use `haveI : IsScalarTower (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `h2` using `Module.finrank_mul_finrank (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q)`. Rewrite `h1` using `[Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finrank, AdjoinRoot.powerBasis_dim]`. Rewrite `h2` using `[finrank_KL Q h hs hsc]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_Kf (h : Good Q) {s : E} (hs : s ≠ 0) (hsc : IsCMField.complexConj E s = -s) :
    Module.finrank (maximalRealSubfield E) (Kf Q h) = Q.natDegree := by
  have h1 := Module.finrank_mul_finrank (maximalRealSubfield E) E (AdjoinRoot Q)
  haveI : IsScalarTower (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h2 := Module.finrank_mul_finrank (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finrank, AdjoinRoot.powerBasis_dim] at h1
  rw [finrank_KL Q h hs hsc] at h2
  omega

end PositivityTheory.Rg.BcB.G3.FactorFieldP

open PositivityTheory.Rg.BcB.G3.FactorFieldP in
/- English proof (translation)
Introduce `E _ _ _ s d hs hsc hd Q _ hmon hQ`. Establish `hS : AdjoinRoot.of Q s ≠ 0` using `(_root_.map_ne_zero _).2 hs`. Establish `hσS : sig Q hQ (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s`. Rewrite using `[sig_of, hsc, map_neg]`. Use `⟨Kf Q hQ, inferInstance, inferInstance, inferInstance, (Kf Q hQ).val.toRingHom, sig Q hQ, totReal Q hQ, finrank_Kf Q hQ hs hsc, fun x => rfl, fun x => sig_of Q hQ x, ?_, fun a => a.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[sig_root, inv_mul_cancel₀]`. Introduce `h0`. Set `ψ : AdjoinRoot Q →+* ℂ` to `Classical.choice (inferInstance : Nonempty _)`. Use `root_norm Q hQ ψ` as an intermediate fact. Rewrite `this` using `[h0, map_zero, norm_zero]`.

Conclude with `zero_ne_one this`. Introduce `z`. Take `⟨a, b, hz⟩` from `decomp Q hQ hS hσS z`. Conclude with `⟨a, b, hz⟩`.
-/
theorem PositivityTheory.Rg.BcB.G3.factorField_pf : FactorField := by
  intro E _ _ _ s d hs hsc hd Q _ hmon hQ
  have hS : AdjoinRoot.of Q s ≠ 0 := (_root_.map_ne_zero _).2 hs
  have hσS : sig Q hQ (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s := by
    rw [sig_of, hsc, map_neg]
  refine ⟨Kf Q hQ, inferInstance, inferInstance, inferInstance, (Kf Q hQ).val.toRingHom, sig Q hQ,
    totReal Q hQ, finrank_Kf Q hQ hs hsc, fun x => rfl, fun x => sig_of Q hQ x, ?_, fun a => a.2, ?_⟩
  · rw [sig_root, inv_mul_cancel₀]
    intro h0
    let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have := root_norm Q hQ ψ
    rw [h0, map_zero, norm_zero] at this
    exact zero_ne_one this
  · intro z
    obtain ⟨a, b, hz⟩ := decomp Q hQ hS hσS z
    exact ⟨a, b, hz⟩
