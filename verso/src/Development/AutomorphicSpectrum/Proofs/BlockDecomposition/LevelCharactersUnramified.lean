import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrLevChars

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ}
  {S : Subring (Fv F v ⊗[F] E)} {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, sigR_smul, map_one]`.
-/
theorem sigR_algebraMap (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  rw [Algebra.algebraMap_eq_smul_one, sigR_smul, map_one]

/- English proof (translation)
Establish `h1 : x ∈ Rv bs v`. Rewrite using `[← hG.carrier]`. Conclude with `hx`. Establish `h2 : β • x ∈ Rv bs v` using `fun k => by`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Conclude with `mul_mem hβ (h1 k)`. Rewrite `h2` using `[← hG.carrier]`. Conclude with `h2`.
-/
theorem smul_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {β : Fv F v} (hβ : β ∈ v.adicCompletionIntegers F)
    {x : Fv F v ⊗[F] E} (hx : x ∈ S) : β • x ∈ S := by
  have h1 : x ∈ Rv bs v := by
    rw [← hG.carrier]
    exact hx
  have h2 : β • x ∈ Rv bs v := fun k => by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hβ (h1 k)
  rw [← hG.carrier] at h2
  exact h2

/- English proof (translation)
The claim follows from `hG.fixed a (by rw [← hG.sig, ha])`.
-/
theorem fixed_eq (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (a : S) (ha : σS a = a) :
    ∃ α : Fv F v, (a : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) α :=
  hG.fixed a (by rw [← hG.sig, ha])

/- English proof (translation)
Establish `h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v` using `fun k => by`. Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Rewrite `h` using `[← hG.carrier]`. Conclude with `h`.
-/
theorem basis_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (i : Fin d) :
    Algebra.TensorProduct.basis (Fv F v) bs i ∈ S := by
  have h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v := fun k => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← hG.carrier] at h
  exact h

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Conclude with `hG.quad.notUnit (isUnit_of_subsingleton _)`.
-/
theorem nontrivial_S (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : Nontrivial S := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hG.quad.notUnit (isUnit_of_subsingleton _)

/- English proof (translation)
Take `⟨u, hu, hb⟩` from `hG.quad.basis`. Establish `: Nontrivial S` using `nontrivial_S hG`. Establish `: Nontrivial (Fv F v ⊗[F] E)` using `(Subtype.val_injective (p := fun x => x ∈ S)).nontrivial`. Establish `hinj` using `(algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective`. Establish `hli : LinearIndependent (Fv F v) ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)]`.

Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t h`. Establish `ht : t = 0`. Assume the negation of the conclusion as `ht`. Establish `e : (u : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (-(t⁻¹ * s))`.

Establish `h3 : t • (u : Fv F v ⊗[F] E) = -(s • (1 : Fv F v ⊗[F] E))` using `eq_neg_of_add_eq_zero_right h`. Establish `h4 : (u : Fv F v ⊗[F] E) = t⁻¹ • (t • (u : Fv F v ⊗[F] E))`. Rewrite using `[smul_smul, inv_mul_cancel₀ ht, one_smul]`. Rewrite using `[h4, h3, Algebra.algebraMap_eq_smul_one, smul_neg, neg_smul, smul_smul]`. Establish `hfix : σS u = u` using `Subtype.ext (by rw [hG.sig, e, sigR_algebraMap])`.

Rewrite `hu` using `[hfix, sub_self, isUnit_zero_iff]`. Conclude with `zero_ne_one hu`. Substitute `ht` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Rewrite `h` using `[zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one]`.

Conclude with `hinj (by rw [h, map_zero])`. Establish `hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)])`. Rewrite using `[← (Algebra.TensorProduct.basis (Fv F v) bs).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨x, y, hx, hy, e⟩` from `hb ⟨_, basis_mem hG i⟩`.

Take `⟨α, hα⟩` from `fixed_eq hG x hx`. Take `⟨β, hβ⟩` from `fixed_eq hG y hy`. Establish `e2 : Algebra.TensorProduct.basis (Fv F v) bs i = α • (1 : Fv F v ⊗[F] E) + β • (u : Fv F v ⊗[F] E)`. Establish `e3` using `congrArg Subtype.val e`. Simplify using `only [Subring.coe_add, Subring.coe_mul] at e3`.

Rewrite using `[e3, hα, hβ, Algebra.smul_def, Algebra.smul_def, mul_one]`. Rewrite using `[SetLike.mem_coe, e2]`. Conclude with `add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))`. Establish `h1` using `Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)`. Establish `h2` using `Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Fv F v) bs)`.

Simplify using `using h2.symm.trans h1`.
-/
theorem card_eq_two (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : d = 2 := by
  obtain ⟨u, hu, hb⟩ := hG.quad.basis
  have : Nontrivial S := nontrivial_S hG
  have : Nontrivial (Fv F v ⊗[F] E) := (Subtype.val_injective (p := fun x => x ∈ S)).nontrivial
  have hinj := (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  have hli : LinearIndependent (Fv F v) ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have ht : t = 0 := by
      by_contra ht
      have e : (u : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (-(t⁻¹ * s)) := by
        have h3 : t • (u : Fv F v ⊗[F] E) = -(s • (1 : Fv F v ⊗[F] E)) := eq_neg_of_add_eq_zero_right h
        have h4 : (u : Fv F v ⊗[F] E) = t⁻¹ • (t • (u : Fv F v ⊗[F] E)) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [h4, h3, Algebra.algebraMap_eq_smul_one, smul_neg, neg_smul, smul_smul]
      have hfix : σS u = u := Subtype.ext (by rw [hG.sig, e, sigR_algebraMap])
      rw [hfix, sub_self, isUnit_zero_iff] at hu
      exact zero_ne_one hu
    subst ht
    refine ⟨?_, rfl⟩
    rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one] at h
    exact hinj (by rw [h, map_zero])
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)]) := by
    rw [← (Algebra.TensorProduct.basis (Fv F v) bs).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, y, hx, hy, e⟩ := hb ⟨_, basis_mem hG i⟩
    obtain ⟨α, hα⟩ := fixed_eq hG x hx
    obtain ⟨β, hβ⟩ := fixed_eq hG y hy
    have e2 : Algebra.TensorProduct.basis (Fv F v) bs i =
        α • (1 : Fv F v ⊗[F] E) + β • (u : Fv F v ⊗[F] E) := by
      have e3 := congrArg Subtype.val e
      simp only [Subring.coe_add, Subring.coe_mul] at e3
      rw [e3, hα, hβ, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [SetLike.mem_coe, e2]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  have h2 := Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Fv F v) bs)
  simpa using h2.symm.trans h1

/- English proof (translation)
Rewrite using `[Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Fv F v) bs), Fintype.card_fin, card_eq_two hG, two_nsmul, two_mul]`.
-/
theorem trace_algebraMap_eq (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Fv F v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (algebraMap (Fv F v) (Fv F v ⊗[F] E) x) = 2 * x := by
  rw [Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Fv F v) bs), Fintype.card_fin,
    card_eq_two hG, two_nsmul, two_mul]

/- English proof (translation)
Unfold `psiF`. Rewrite using `[← Algebra.smul_def, map_smul, smul_eq_mul, ← mul_assoc ((ϖ ^ (k + 1))⁻¹), pow_succ, mul_inv, mul_assoc (ϖ ^ k)⁻¹, inv_mul_cancel₀ hG.unif_ne, mul_one]`.
-/
theorem psiF_compat (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (c : Fv F v) (k : ℕ) (a : Fv F v ⊗[F] E) :
    psiF ψv ϖ c (k + 1) (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * a) = psiF ψv ϖ c k a := by
  unfold psiF
  rw [← Algebra.smul_def, map_smul, smul_eq_mul, ← mul_assoc ((ϖ ^ (k + 1))⁻¹), pow_succ, mul_inv,
    mul_assoc (ϖ ^ k)⁻¹, inv_mul_cancel₀ hG.unif_ne, mul_one]

/- English proof (translation)
Establish `h20 : (2 : Fv F v) ≠ 0`. Introduce `h`. Use `hG.two` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this`.

Take `⟨α, hα⟩` from `fixed_eq hG a ha`. Establish `hαO : α ∈ v.adicCompletionIntegers F`. Establish `h2` using `hG.trace_mem a.2`. Rewrite `h2` using `[hα, trace_algebraMap_eq hG]`. Establish `h3` using `mul_mem hG.half_mem h2`.

Rewrite `h3` using `[← mul_assoc, inv_mul_cancel₀ h20, one_mul]`. Then use the resulting hypothesis. Establish `hkey : c * (ϖ⁻¹ * α) ∈ v.adicCompletionIntegers F`. Use `(hG.psi_cond _).1 fun β hβ => ?_` and prove the remaining obligations. Establish `hbS : algebraMap (Fv F v) (Fv F v ⊗[F] E) β ∈ S`. Establish `h1` using `smul_mem hG hβ (one_mem S)`.

Rewrite `h1` using `[← Algebra.algebraMap_eq_smul_one]`. Then use the resulting hypothesis. Establish `hfix : σS ⟨_, hbS⟩ = ⟨_, hbS⟩` using `Subtype.ext (by rw [hG.sig]; exact sigR_algebraMap β)`. Establish `h1` using `hb _ hfix`. Rewrite `h1` using `[hG.psiLev_mk]`. Establish `e : ((a * ⟨_, hbS⟩ : S) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (α * β)`.

Rewrite using `[Subring.coe_mul, hα, map_mul]`. Rewrite `h1` using `[e]`. Unfold `psiF at h1`. Rewrite `h1` using `[trace_algebraMap_eq hG]`. Rewrite using `[← h1]`.

Use `congr 1`. Use `hG.unif_ne` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish `hγ : ϖ⁻¹ * α ∈ v.adicCompletionIntegers F`. Rewrite `hkey`, the goal using `[HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]`.

Rewrite `hkey` using `[norm_mul, hc1, one_mul]`. Conclude with `hkey`. Establish `hgS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) ∈ S`. Establish `h1` using `smul_mem hG hγ (one_mem S)`. Rewrite `h1` using `[← Algebra.algebraMap_eq_smul_one]`. Then use the resulting hypothesis.

Use `Ideal.mem_span_singleton'.2 ⟨⟨_, hgS⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, Subring.coe_mul, hα]`. Use `show algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = _`. Rewrite using `[← map_mul]`. Use `congr 1`.

Use `hG.unif_ne` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem mem_level_of_character_trivial (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (hc1 : ‖c‖ = 1) (a : S) (ha : σS a = a)
    (hb : ∀ b, σS b = b → hG.psiLev hc 1 (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev hG.pS 1 := by
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h
    have := hG.two
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨α, hα⟩ := fixed_eq hG a ha
  have hαO : α ∈ v.adicCompletionIntegers F := by
    have h2 := hG.trace_mem a.2
    rw [hα, trace_algebraMap_eq hG] at h2
    have h3 := mul_mem hG.half_mem h2
    rwa [← mul_assoc, inv_mul_cancel₀ h20, one_mul] at h3
  have hkey : c * (ϖ⁻¹ * α) ∈ v.adicCompletionIntegers F := by
    refine (hG.psi_cond _).1 fun β hβ => ?_
    have hbS : algebraMap (Fv F v) (Fv F v ⊗[F] E) β ∈ S := by
      have h1 := smul_mem hG hβ (one_mem S)
      rwa [← Algebra.algebraMap_eq_smul_one] at h1
    have hfix : σS ⟨_, hbS⟩ = ⟨_, hbS⟩ := Subtype.ext (by rw [hG.sig]; exact sigR_algebraMap β)
    have h1 := hb _ hfix
    rw [hG.psiLev_mk] at h1
    have e : ((a * ⟨_, hbS⟩ : S) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (α * β) := by
      rw [Subring.coe_mul, hα, map_mul]
    rw [e] at h1
    unfold psiF at h1
    rw [trace_algebraMap_eq hG] at h1
    rw [← h1]
    congr 1
    have := hG.unif_ne
    field_simp
  have hγ : ϖ⁻¹ * α ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff] at hkey ⊢
    rw [norm_mul, hc1, one_mul] at hkey
    exact hkey
  have hgS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) ∈ S := by
    have h1 := smul_mem hG hγ (one_mem S)
    rwa [← Algebra.algebraMap_eq_smul_one] at h1
  refine Ideal.mem_span_singleton'.2 ⟨⟨_, hgS⟩, Subtype.ext ?_⟩
  rw [pow_one, Subring.coe_mul, hα]
  show algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = _
  rw [← map_mul]
  congr 1
  have := hG.unif_ne
  field_simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG c hc hc1`. Use `⟨fun k a => ?_, fun a ha hb => mem_level_of_character_trivial hG hc hc1 a ha hb⟩` and prove the remaining obligations. Rewrite using `[GoodLoc.psiLev_mk, GoodLoc.psiLev_mk]`. Conclude with `psiF_compat hG c k a`.
-/
theorem levChars : PositivityTheory.SiegelWeilFormula.Gunr.LevChars := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG c hc hc1
  refine ⟨fun k a => ?_, fun a ha hb => mem_level_of_character_trivial hG hc hc1 a ha hb⟩
  rw [GoodLoc.psiLev_mk, GoodLoc.psiLev_mk]
  exact psiF_compat hG c k a

end GlobalTheory.CompanionTheory.GunrLevChars

end
