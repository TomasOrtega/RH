import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormSep
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartPointSeparable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `F _ _ n e I f t p _ K L _ _ _ _ _ _ _ _ _ _ hI hf _`. Set `S` to `MvPolynomial (Fin e × Fin n) F`. Set `O` to `Localization.AtPrime p`. Set `Sg` to `ChartInc I t e`. Set `CL` to `ChartLoc I t e p`.

Set `φ : S →+* K` to `(algebraMap O K).comp (algebraMap S O)`. Set `_ : Algebra F K` to `(φ.comp (algebraMap F S)).toAlgebra`. Set `_ : Algebra F L` to `((algebraMap K L).comp (algebraMap F K)).toAlgebra`. Establish `: IsScalarTower F K L` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `u : Fin e × Fin n → K` to `fun q => φ (X q)`.

Set `ψ : Sg →+* L` to `(algebraMap CL L).comp (algebraMap Sg CL)`. Set `mk : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* Sg` to `Ideal.Quotient.mk (chartIncIdeal I t e)`. Establish `hmk0 : ∀ P, P ∈ chartIncIdeal I t e → mk P = 0` using `fun P hP => Ideal.Quotient.eq_zero_iff_mem.2 hP`. Set `η : Fin n → L` to `fun m => ψ (chartX I t e (X m))`. Establish `hφinj : Function.Injective φ` using `(IsFractionRing.injective O K).comp (IsLocalization.injective O (M := p.primeCompl) p.primeCompl_le_nonZeroDivisors)`.

Establish `hφ : ∀ a, φ a = aeval u a`. Introduce `a`. Establish `: φ = (aeval u : S →ₐ[F] K).toRingHom` using `MvPolynomial.ringHom_ext (fun c => by simp; rfl) (fun q => by simp [u])`. Rewrite using `[this]`. Both sides reduce to the same expression.

Establish `hψS : ∀ s : S, ψ (algebraMap S Sg s) = algebraMap K L (φ s)`. Introduce `s`. Simplify using `only [ψ, φ, RingHom.comp_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply S Sg CL, IsScalarTower.algebraMap_apply S O CL, ← IsScalarTower.algebraMap_apply O CL L, IsScalarTower.algebraMap_apply O K L]`. Establish `hmkS : ∀ s : S, mk (rename Sum.inr s) = algebraMap S Sg s` using `fun s => rfl`.

Establish `hC : ∀ c : F, ψ (mk (C c)) = algebraMap F L c`. Introduce `c`. Rewrite using `[← rename_C Sum.inr, hmkS, hψS]`. Both sides reduce to the same expression. Establish `hXl : ∀ m, ψ (mk (X (Sum.inl m))) = η m`.

Introduce `m`. Use `show ψ (mk (X (Sum.inl m))) = ψ (mk (rename Sum.inl (X m)))`. Rewrite using `[rename_X]`. Establish `hXr : ∀ q, ψ (mk (X (Sum.inr q))) = algebraMap K L (u q)`. Introduce `q`.

Rewrite using `[← rename_X Sum.inr, hmkS, hψS]`. Establish `hψX : ∀ g, ψ (chartX I t e g) = aeval η g`. Introduce `g`. Establish `: ψ.comp (chartX I t e) = (aeval η : MvPolynomial (Fin n) F →ₐ[F] L).toRingHom` using `MvPolynomial.ringHom_ext (fun c => by show ψ (mk (rename Sum.inl (C c))) = _`. Rewrite using `[rename_C, hC]`.

Use the proof step `simp) (fun m => by simp [η])`. Conclude with `congrArg (fun r : MvPolynomial (Fin n) F →+* L => r g) this`. Establish `hzero : ∀ g ∈ I ⊔ Ideal.span {linForm t - 1}, chartX I t e g = 0`. Introduce `g hg`. Conclude with `hmk0 _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))`.

Establish `hIη : ∀ g ∈ I, aeval η g = 0` using `fun g hg => by`. Rewrite using `[← hψX, hzero g (Ideal.mem_sup_left hg), map_zero]`. Establish `hU : ∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0`. Introduce `i`. Establish `hmem : ∑ m, X (Sum.inr (i, m)) * X (Sum.inl m) ∈ chartIncIdeal I t e` using `Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)`.

Use `congrArg ψ (hmk0 _ hmem)` as an intermediate fact. Rewrite `this` using `[map_zero, map_sum, map_sum]`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hXr, hXl]`.

Establish `hT : ∑ m, algebraMap F L (t m) * η m = 1`. Establish `h1` using `hzero (linForm t - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Rewrite `h1` using `[map_sub, map_one, sub_eq_zero]`. Use `congrArg ψ h1` as an intermediate fact. Rewrite `this` using `[map_one, hψX]`.

Rewrite using `[← this]`. Simplify using `[linForm]`. Establish `hK : IntermediateField.adjoin F (Set.range u) = ⊤`. Establish `hmemS : ∀ s : S, φ s ∈ IntermediateField.adjoin F (Set.range u)` using `fun s => by`. Rewrite using `[hφ]`.

Apply `IntermediateField.algebra_adjoin_le_adjoin` to reduce the goal to its premises. Rewrite using `[Algebra.adjoin_range_eq_range_aeval]`. Conclude with `⟨s, rfl⟩`. Establish `hmemO : ∀ a : O, algebraMap O K a ∈ IntermediateField.adjoin F (Set.range u)` using `fun a => by`. Take `⟨⟨s, s', hs'⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl a`.

Simplify using `only`. Establish `hs0 : φ s' ≠ 0` using `fun h0 => hs' (by`. Rewrite using `[hφinj (h0.trans (map_zero φ).symm)]`. Conclude with `p.zero_mem)`. Establish `hspec` using `congrArg (algebraMap O K) (IsLocalization.mk'_spec O s ⟨s', hs'⟩)`.

Rewrite `hspec` using `[map_mul]`. Rewrite using `[eq_div_of_mul_eq hs0 hspec]`. Conclude with `div_mem (hmemS s) (hmemS s')`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Take `⟨a, b, _, rfl⟩` from `IsFractionRing.div_surjective (A := O) x`.

Conclude with `div_mem (hmemO a) (hmemO b)`. Establish `hη : IntermediateField.adjoin K (Set.range η) = ⊤` using `by set E := IntermediateField.adjoin K (Set.range η)`. Establish `hmemSg : ∀ σ : Sg, ψ σ ∈ E`. Introduce `σ`. Take `⟨P, rfl⟩ : ∃ P, mk P = σ` from `Ideal.Quotient.mk_surjective σ`.

Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C c`. Rewrite using `[hC, IsScalarTower.algebraMap_apply F K L]`. Conclude with `E.algebraMap_mem _`. Consider the case `add a b ha hb`.

Rewrite using `[map_add, map_add]`. Conclude with `add_mem ha hb`. Consider the case `mul_X a v ha`. Rewrite using `[map_mul, map_mul]`. Use `mul_mem ha ?_` and prove the remaining obligations.

Break down `v with m | q` into its components or cases. Rewrite using `[hXl]`. Conclude with `IntermediateField.subset_adjoin K _ ⟨m, rfl⟩`. Rewrite using `[hXr]`. Conclude with `E.algebraMap_mem _`.

Establish `hmemCL : ∀ c : CL, algebraMap CL L c ∈ E` using `fun c => by`. Take `⟨⟨σ, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid Sg p.primeCompl) c`. Simplify using `only`. Take `⟨s0, hs0, hs⟩` from `s.2`. Establish `hne : ψ s.1 ≠ 0`.

Rewrite using `[← hs]`. Rewrite using `[hψS]`. Use `(map_ne_zero _).2 fun h0 => hs0 ?_` and prove the remaining obligations. Rewrite using `[hφinj (h0.trans (map_zero φ).symm)]`. Conclude with `p.zero_mem`.

Establish `hspec` using `congrArg (algebraMap CL L) (IsLocalization.mk'_spec CL σ s)`. Rewrite `hspec` using `[map_mul]`. Rewrite using `[eq_div_of_mul_eq hne hspec]`. Conclude with `div_mem (hmemSg σ) (hmemSg _)`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations.

Take `⟨a, b, _, rfl⟩` from `IsFractionRing.div_surjective (A := CL) y`. Conclude with `div_mem (hmemCL a) (hmemCL b)`. Establish `halg : AlgebraicIndependent F u`. Establish `hinj : Function.Injective (aeval u : S →ₐ[F] K)` using `fun a b hab => hφinj (by rw [hφ, hφ]; exact hab)`. Establish `h0` using `(MvPolynomial.algebraicIndependent_X (Fin e × Fin n) F).map' hinj`.

Establish `hc : (⇑(aeval u : S →ₐ[F] K) ∘ X) = u`. Use function extensionality and compare the values at `q`. Simplify using `only [Function.comp_apply, aeval_X]`. Rewrite `h0` using `[hc]`. Then use the resulting hypothesis. Conclude with `h F n e K L u t η halg hK hη hU hT fun j₀ hj₀ => Vertical.ChartPointTrdeg.full F L n e I f hI hf η j₀ hIη hj₀`.
-/
theorem ChartFracSeparable.proof (h : ChartPointSeparable.Statement) : ChartFracSeparable.Statement := by
  intro F _ _ n e I f t p _ K L _ _ _ _ _ _ _ _ _ _ hI hf _

  let S := MvPolynomial (Fin e × Fin n) F
  let O := Localization.AtPrime p
  let Sg := ChartInc I t e
  let CL := ChartLoc I t e p
  let φ : S →+* K := (algebraMap O K).comp (algebraMap S O)
  let _ : Algebra F K := (φ.comp (algebraMap F S)).toAlgebra
  let _ : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let u : Fin e × Fin n → K := fun q => φ (X q)
  let ψ : Sg →+* L := (algebraMap CL L).comp (algebraMap Sg CL)
  let mk : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* Sg := Ideal.Quotient.mk (chartIncIdeal I t e)
  have hmk0 : ∀ P, P ∈ chartIncIdeal I t e → mk P = 0 := fun P hP => Ideal.Quotient.eq_zero_iff_mem.2 hP
  let η : Fin n → L := fun m => ψ (chartX I t e (X m))
  have hφinj : Function.Injective φ :=
    (IsFractionRing.injective O K).comp
      (IsLocalization.injective O (M := p.primeCompl) p.primeCompl_le_nonZeroDivisors)
  have hφ : ∀ a, φ a = aeval u a := by
    intro a
    have : φ = (aeval u : S →ₐ[F] K).toRingHom :=
      MvPolynomial.ringHom_ext (fun c => by simp; rfl) (fun q => by simp [u])
    rw [this]
    rfl

  have hψS : ∀ s : S, ψ (algebraMap S Sg s) = algebraMap K L (φ s) := by
    intro s
    simp only [ψ, φ, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply S Sg CL, IsScalarTower.algebraMap_apply S O CL,
      ← IsScalarTower.algebraMap_apply O CL L, IsScalarTower.algebraMap_apply O K L]
  have hmkS : ∀ s : S, mk (rename Sum.inr s) = algebraMap S Sg s :=
    fun s => rfl
  have hC : ∀ c : F, ψ (mk (C c)) = algebraMap F L c := by
    intro c
    rw [← rename_C Sum.inr, hmkS, hψS]
    rfl
  have hXl : ∀ m, ψ (mk (X (Sum.inl m))) = η m := by
    intro m
    show ψ (mk (X (Sum.inl m))) = ψ (mk (rename Sum.inl (X m)))
    rw [rename_X]
  have hXr : ∀ q, ψ (mk (X (Sum.inr q))) = algebraMap K L (u q) := by
    intro q
    rw [← rename_X Sum.inr, hmkS, hψS]

  have hψX : ∀ g, ψ (chartX I t e g) = aeval η g := by
    intro g
    have : ψ.comp (chartX I t e) = (aeval η : MvPolynomial (Fin n) F →ₐ[F] L).toRingHom :=
      MvPolynomial.ringHom_ext (fun c => by
        show ψ (mk (rename Sum.inl (C c))) = _
        rw [rename_C, hC]
        simp) (fun m => by simp [η])
    exact congrArg (fun r : MvPolynomial (Fin n) F →+* L => r g) this
  have hzero : ∀ g ∈ I ⊔ Ideal.span {linForm t - 1}, chartX I t e g = 0 := by
    intro g hg
    exact hmk0 _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))
  have hIη : ∀ g ∈ I, aeval η g = 0 := fun g hg => by
    rw [← hψX, hzero g (Ideal.mem_sup_left hg), map_zero]

  have hU : ∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0 := by
    intro i
    have hmem : ∑ m, X (Sum.inr (i, m)) * X (Sum.inl m) ∈ chartIncIdeal I t e :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
    have := congrArg ψ (hmk0 _ hmem)
    rw [map_zero, map_sum, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_mul, hXr, hXl]
  have hT : ∑ m, algebraMap F L (t m) * η m = 1 := by
    have h1 := hzero (linForm t - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [map_sub, map_one, sub_eq_zero] at h1
    have := congrArg ψ h1
    rw [map_one, hψX] at this
    rw [← this]
    simp [linForm]

  have hK : IntermediateField.adjoin F (Set.range u) = ⊤ := by
    have hmemS : ∀ s : S, φ s ∈ IntermediateField.adjoin F (Set.range u) := fun s => by
      rw [hφ]
      apply IntermediateField.algebra_adjoin_le_adjoin
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨s, rfl⟩
    have hmemO : ∀ a : O, algebraMap O K a ∈ IntermediateField.adjoin F (Set.range u) := fun a => by
      obtain ⟨⟨s, s', hs'⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
      dsimp only
      have hs0 : φ s' ≠ 0 := fun h0 => hs' (by
        rw [hφinj (h0.trans (map_zero φ).symm)]
        exact p.zero_mem)
      have hspec := congrArg (algebraMap O K) (IsLocalization.mk'_spec O s ⟨s', hs'⟩)
      rw [map_mul] at hspec
      rw [eq_div_of_mul_eq hs0 hspec]
      exact div_mem (hmemS s) (hmemS s')
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    exact div_mem (hmemO a) (hmemO b)

  have hη : IntermediateField.adjoin K (Set.range η) = ⊤ := by
    set E := IntermediateField.adjoin K (Set.range η)
    have hmemSg : ∀ σ : Sg, ψ σ ∈ E := by
      intro σ
      obtain ⟨P, rfl⟩ : ∃ P, mk P = σ := Ideal.Quotient.mk_surjective σ
      induction P using MvPolynomial.induction_on with
      | C c =>
        rw [hC, IsScalarTower.algebraMap_apply F K L]
        exact E.algebraMap_mem _
      | add a b ha hb =>
        rw [map_add, map_add]
        exact add_mem ha hb
      | mul_X a v ha =>
        rw [map_mul, map_mul]
        refine mul_mem ha ?_
        rcases v with m | q
        · rw [hXl]
          exact IntermediateField.subset_adjoin K _ ⟨m, rfl⟩
        · rw [hXr]
          exact E.algebraMap_mem _
    have hmemCL : ∀ c : CL, algebraMap CL L c ∈ E := fun c => by
      obtain ⟨⟨σ, s⟩, rfl⟩ := IsLocalization.mk'_surjective
        (Algebra.algebraMapSubmonoid Sg p.primeCompl) c
      dsimp only
      obtain ⟨s0, hs0, hs⟩ := s.2
      have hne : ψ s.1 ≠ 0 := by
        rw [← hs]
        rw [hψS]
        refine (map_ne_zero _).2 fun h0 => hs0 ?_
        rw [hφinj (h0.trans (map_zero φ).symm)]
        exact p.zero_mem
      have hspec := congrArg (algebraMap CL L) (IsLocalization.mk'_spec CL σ s)
      rw [map_mul] at hspec
      rw [eq_div_of_mul_eq hne hspec]
      exact div_mem (hmemSg σ) (hmemSg _)
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := CL) y
    exact div_mem (hmemCL a) (hmemCL b)

  have halg : AlgebraicIndependent F u := by
    have hinj : Function.Injective (aeval u : S →ₐ[F] K) := fun a b hab =>
      hφinj (by rw [hφ, hφ]; exact hab)
    have h0 := (MvPolynomial.algebraicIndependent_X (Fin e × Fin n) F).map' hinj
    have hc : (⇑(aeval u : S →ₐ[F] K) ∘ X) = u := by
      funext q
      simp only [Function.comp_apply, aeval_X]
    rwa [hc] at h0
  exact h F n e K L u t η halg hK hη hU hT fun j₀ hj₀ =>
    Vertical.ChartPointTrdeg.full F L n e I f hI hf η j₀ hIη hj₀

end

end GroundTheory.Heights₂.Heights
