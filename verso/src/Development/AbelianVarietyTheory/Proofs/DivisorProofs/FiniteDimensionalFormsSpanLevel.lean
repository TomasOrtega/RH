import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetSeparatingFiniteDimensionalFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainRationalBlockUnipotentGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalConstTerm

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory

namespace GlobalTheory.HCFGLct

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E`. Take `⟨𝓕, h𝓕, h0, hT⟩` from `GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN E a r (Measure.addHaar : Measure (BlockIx a r → Ad E))`. Use `⟨((Measure.addHaar : Measure (BlockIx a r → Ad E)) 𝓕)⁻¹ • Measure.addHaar, 𝓕, ?_, h𝓕.mono Measure.smul_absolutelyContinuous, ?_⟩` and prove the remaining obligations. Conclude with `Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hT.ne) (ENNReal.inv_ne_top.2 h0)`.

Rewrite using `[Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hT.ne]`.
-/
theorem exists_haar_fd_one (r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] :
    ∃ (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratN E a r) 𝓕 μ ∧ μ 𝓕 = 1 := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  obtain ⟨𝓕, h𝓕, h0, hT⟩ := GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN E a r
    (Measure.addHaar : Measure (BlockIx a r → Ad E))
  refine ⟨((Measure.addHaar : Measure (BlockIx a r → Ad E)) 𝓕)⁻¹ • Measure.addHaar, 𝓕, ?_,
    h𝓕.mono Measure.smul_absolutelyContinuous, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hT.ne) (ENNReal.inv_ne_top.2 h0)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hT.ne]

/- English proof (translation)
Introduce `m' hm' μ 𝓕 hμ h𝓕 g`. Take `rfl : m' = m` from `hm'.measurable_eq.trans hm.measurable_eq.symm`. Use `haveI := hμ`. Use `haveI := hμ₀`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E`. Use `haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm`. Use `haveI : Countable (ratN E a r) := by`. Establish `: ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r))` using `AddMonoidHom.coe_range _`.

Express the relevant statement in the definitionally equal form `Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))`. Rewrite using `[this]`. Conclude with `(Set.countable_range _).to_subtype`. Establish `hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), φ (unip (γ +ᵥ x) * g) = φ (unip x * g)`. Introduce and unpack `⟨_, e, rfl⟩ x`.

Express the relevant statement in the definitionally equal form `φ (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = φ (unip x * g)`. Rewrite using `[unip_add, unip_algebraMap, mul_assoc, hl]`. Establish `h𝓕' : IsAddFundamentalDomain (ratN E a r) 𝓕 μ₀` using `h𝓕.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)`. Rewrite using `[Measure.isAddLeftInvariant_eq_smul μ μ₀, Measure.restrict_smul, integral_smul_nnreal_measure, h𝓕'.setIntegral_eq h𝓕₀ (f := fun x => φ (unip x * g)) hinv, hz, smul_zero]`.
-/
theorem setIntegral_eq_zero_all {r : ℕ} [m : MeasurableSpace (BlockIx a r → Ad E)] [hm : BorelSpace (BlockIx a r → Ad E)]
    (μ₀ : Measure (BlockIx a r → Ad E)) (𝓕₀ : Set (BlockIx a r → Ad E)) (hμ₀ : μ₀.IsAddHaarMeasure)
    (h𝓕₀ : IsAddFundamentalDomain (ratN E a r) 𝓕₀ μ₀) (φ : GA E a → ℂ) (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (hz : ∀ g, ∫ x in 𝓕₀, φ (unip x * g) ∂μ₀ = 0) :
    ∀ [m' : MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
      (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
      ∀ g, ∫ x in 𝓕, φ (unip x * g) ∂μ = 0 := by
  intro m' hm' μ 𝓕 hμ h𝓕 g
  obtain rfl : m' = m := hm'.measurable_eq.trans hm.measurable_eq.symm
  haveI := hμ
  haveI := hμ₀
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  have hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), φ (unip (γ +ᵥ x) * g) = φ (unip x * g) := by
    rintro ⟨_, e, rfl⟩ x
    change φ (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = φ (unip x * g)
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  have h𝓕' : IsAddFundamentalDomain (ratN E a r) 𝓕 μ₀ :=
    h𝓕.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  rw [Measure.isAddLeftInvariant_eq_smul μ μ₀, Measure.restrict_smul, integral_smul_nnreal_measure,
    h𝓕'.setIntegral_eq h𝓕₀ (f := fun x => φ (unip x * g)) hinv, hz, smul_zero]

/- English proof (translation)
Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left⟩`. Consider the case `zero => exact ⟨continuous_const, fun _ _ => rfl⟩`. Consider the case `add x y _ _ hx hy => exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2 γ h) (hy.2 γ h)⟩`. Consider the case `smul c x _ hx => exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2 γ h)⟩`.
-/
theorem cont_left_of_mem_span {L : Subgroup (GL (Fin a) (Af E))} {W : Submodule ℂ (Kinf E a → ℂ)}
    {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ} {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    Continuous φ.1 ∧ ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left⟩
  | zero => exact ⟨continuous_const, fun _ _ => rfl⟩
  | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2 γ h) (hy.2 γ h)⟩
  | smul c x _ hx => exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2 γ h)⟩

/- English proof (translation)
Introduce `E _ _ _ a ih L hL W hW χ N`. Use `set V := Submodule.span ℂ (formsGL E a L W {χ} N) with hVdef`. Set `ι` to `{r : Fin a // 0 < (r : ℕ)}`. Establish `key : ∀ i : ι, ∃ c : Sm E a → GA E a → ℂ, (∀ φ ∈ V, ∀ ψ ∈ V, c (φ + ψ) = c φ + c ψ) ∧ (∀ (t : ℂ) (φ : Sm E a), c (t • φ) = t • c φ) ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun φ : V => c φ.1)) ∧ ∀ φ ∈ V, c φ = 0 → ∀ [MeasurableSpace (BlockIx a (i.1 : ℕ) → Ad E)] [Borel …`. Introduce `i`.

Use `letI mB : MeasurableSpace (BlockIx a (i.1 : ℕ) → Ad E) := borel _`. Use `haveI hB : BorelSpace (BlockIx a (i.1 : ℕ) → Ad E) := ⟨rfl⟩`. Take `⟨μ, 𝓕, hμ, h𝓕, h1⟩` from `exists_haar_fd_one (E := E) (a := a) (i.1 : ℕ)`. Use `haveI := hμ`. Use `⟨fun φ g => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ, fun φ hφ ψ hψ => ?_, fun t φ => ?_, ?_, fun φ hφ h0 => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `g`. Take `⟨hc, hl⟩` from `cont_left_of_mem_span hφ`. Take `⟨hc', hl'⟩` from `cont_left_of_mem_span hψ`. Conclude with `integral_add (CuspidalL2GL.integrableOn_unip hc hl μ h𝓕 g) (CuspidalL2GL.integrableOn_unip hc' hl' μ h𝓕 g)`. Use function extensionality and compare the values at `g`.

Conclude with `integral_const_mul t _`. Conclude with `GlobalTheory.HCFct.finiteDimensional_constTerm E a ih L hL W hW {χ} (Set.finite_singleton χ) N i.1 i.2 i.1.isLt μ 𝓕 hμ h𝓕 h1`. Conclude with `setIntegral_eq_zero_all (m := mB) (hm := hB) μ 𝓕 hμ h𝓕 φ.1 (cont_left_of_mem_span hφ).2 (fun g => congrFun h0 g)`. Use `choose c hadd hsmul hfin hzero using key`. Set `Λ : V →ₗ[ℂ] (ι × GA E a → ℂ)` to `{ toFun := fun φ p => c p.1 φ.1 p.2 map_add' := fun φ ψ => funext fun p => congrFun (hadd p.1 φ.1 φ.2 ψ.1 ψ.2) p.2 map_smul' := fun t φ => funext fun p => congrFun (hsmul p.1 t φ.1) p.2 }`.

Set `S : ι → Submodule ℂ (GA E a → ℂ)` to `fun i => Submodule.span ℂ (Set.range fun φ : V => c i φ.1)`. Use `haveI : ∀ i, FiniteDimensional ℂ (S i) := hfin`. Set `U : ((i : ι) → S i) →ₗ[ℂ] (ι × GA E a → ℂ)` to `{ toFun := fun f p => (f p.1).1 p.2 map_add' := fun f f' => rfl map_smul' := fun t f => rfl }`. Establish `hmem : ∀ φ : V, Λ φ ∈ LinearMap.range U` using `fun φ => ⟨fun i => ⟨c i φ.1, Submodule.subset_span ⟨φ, rfl⟩⟩, rfl⟩`. Take `⟨s, hs⟩` from `GlobalTheory.finiteDim_functions_detected_by_finset (ι × GA E a) (LinearMap.range U) inferInstance`.

Set `e` to `s.equivFin`. Set `T₀ : V →ₗ[ℂ] (Fin s.card → ℂ)` to `LinearMap.pi fun j => (LinearMap.proj (e.symm j).1).comp Λ`. Take `⟨T, hT⟩` from `LinearMap.exists_extend T₀`. Use `⟨s.card, T, fun φ hφ h0 => ?_⟩` and prove the remaining obligations. Establish `hV : φ ∈ V` using `Submodule.subset_span hφ`.

Establish `hT0 : T₀ ⟨φ, hV⟩ = 0`. Rewrite using `[← hT]`. Conclude with `h0`. Establish `hΛ : Λ ⟨φ, hV⟩ = 0` using `hs _ (hmem _) fun p hp => by`. Use `congrFun hT0 (e ⟨p, hp⟩)` as an intermediate fact.

Simplify `this` using `[T₀]`. Introduce `r h0' h1'`. Conclude with `hzero ⟨⟨r, h1'⟩, h0'⟩ φ hV (funext fun g => congrFun hΛ (⟨⟨r, h1'⟩, h0'⟩, g))`.
-/
theorem exists_ct_map : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ b < a, ∀ L : Subgroup (GL (Fin b) (Af E)), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (formsGL E b L W X N))) → ∀ L : Subgroup (GL (Fin a) (Af E)), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ), ∃ (n : ℕ) (T : Sm E a →ₗ[ℂ] (Fin n → ℂ)), ∀ φ ∈ formsGL E a L W {χ} N, T φ = 0 → IsCuspidal φ.1 := by
  intro E _ _ _ a ih L hL W hW χ N
  classical
  set V := Submodule.span ℂ (formsGL E a L W {χ} N) with hVdef
  let ι := {r : Fin a // 0 < (r : ℕ)}
  have key : ∀ i : ι, ∃ c : Sm E a → GA E a → ℂ,
      (∀ φ ∈ V, ∀ ψ ∈ V, c (φ + ψ) = c φ + c ψ) ∧ (∀ (t : ℂ) (φ : Sm E a), c (t • φ) = t • c φ) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun φ : V => c φ.1)) ∧
      ∀ φ ∈ V, c φ = 0 → ∀ [MeasurableSpace (BlockIx a (i.1 : ℕ) → Ad E)] [BorelSpace (BlockIx a (i.1 : ℕ) → Ad E)]
        (μ : Measure (BlockIx a (i.1 : ℕ) → Ad E)) (𝓕 : Set (BlockIx a (i.1 : ℕ) → Ad E)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratN E a i.1) 𝓕 μ → ∀ g, ∫ x in 𝓕, φ.1 (unip x * g) ∂μ = 0 := by
    intro i
    letI mB : MeasurableSpace (BlockIx a (i.1 : ℕ) → Ad E) := borel _
    haveI hB : BorelSpace (BlockIx a (i.1 : ℕ) → Ad E) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := exists_haar_fd_one (E := E) (a := a) (i.1 : ℕ)
    haveI := hμ
    refine ⟨fun φ g => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ, fun φ hφ ψ hψ => ?_, fun t φ => ?_, ?_, fun φ hφ h0 => ?_⟩
    · funext g
      obtain ⟨hc, hl⟩ := cont_left_of_mem_span hφ
      obtain ⟨hc', hl'⟩ := cont_left_of_mem_span hψ
      exact integral_add (CuspidalL2GL.integrableOn_unip hc hl μ h𝓕 g) (CuspidalL2GL.integrableOn_unip hc' hl' μ h𝓕 g)
    · funext g
      exact integral_const_mul t _
    · exact GlobalTheory.HCFct.finiteDimensional_constTerm E a ih L hL W hW {χ} (Set.finite_singleton χ) N i.1 i.2 i.1.isLt
        μ 𝓕 hμ h𝓕 h1
    · exact setIntegral_eq_zero_all (m := mB) (hm := hB) μ 𝓕 hμ h𝓕 φ.1 (cont_left_of_mem_span hφ).2 (fun g => congrFun h0 g)
  choose c hadd hsmul hfin hzero using key
  let Λ : V →ₗ[ℂ] (ι × GA E a → ℂ) :=
    { toFun := fun φ p => c p.1 φ.1 p.2
      map_add' := fun φ ψ => funext fun p => congrFun (hadd p.1 φ.1 φ.2 ψ.1 ψ.2) p.2
      map_smul' := fun t φ => funext fun p => congrFun (hsmul p.1 t φ.1) p.2 }
  let S : ι → Submodule ℂ (GA E a → ℂ) := fun i => Submodule.span ℂ (Set.range fun φ : V => c i φ.1)
  haveI : ∀ i, FiniteDimensional ℂ (S i) := hfin
  let U : ((i : ι) → S i) →ₗ[ℂ] (ι × GA E a → ℂ) :=
    { toFun := fun f p => (f p.1).1 p.2
      map_add' := fun f f' => rfl
      map_smul' := fun t f => rfl }
  have hmem : ∀ φ : V, Λ φ ∈ LinearMap.range U := fun φ =>
    ⟨fun i => ⟨c i φ.1, Submodule.subset_span ⟨φ, rfl⟩⟩, rfl⟩
  obtain ⟨s, hs⟩ := GlobalTheory.finiteDim_functions_detected_by_finset (ι × GA E a) (LinearMap.range U) inferInstance
  let e := s.equivFin
  let T₀ : V →ₗ[ℂ] (Fin s.card → ℂ) := LinearMap.pi fun j => (LinearMap.proj (e.symm j).1).comp Λ
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀
  refine ⟨s.card, T, fun φ hφ h0 => ?_⟩
  have hV : φ ∈ V := Submodule.subset_span hφ
  have hT0 : T₀ ⟨φ, hV⟩ = 0 := by
    rw [← hT]; exact h0
  have hΛ : Λ ⟨φ, hV⟩ = 0 := hs _ (hmem _) fun p hp => by
    have := congrFun hT0 (e ⟨p, hp⟩)
    simpa [T₀] using this
  intro r h0' h1'
  exact hzero ⟨⟨r, h1'⟩, h0'⟩ φ hV (funext fun g => congrFun hΛ (⟨⟨r, h1'⟩, h0'⟩, g))

end GlobalTheory.HCFGLct
