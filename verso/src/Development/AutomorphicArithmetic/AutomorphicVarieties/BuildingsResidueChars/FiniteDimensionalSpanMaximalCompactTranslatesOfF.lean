import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

/- English proof (translation)
Introduce `K _ _ n D f hf hfix`. Take `⟨-, -, 𝒜, hfd, -, hA⟩` from `typeFin D`. Use `haveI := hfd`. Take `⟨O, hO, hUO⟩` from `D.isOpen`. Use `haveI : CompactSpace (KG K n) := isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1`.

Set `W : Subgroup (KG K n)` to `D.U.subgroupOf (KG K n)`. Establish `hWo : IsOpen (W : Set (KG K n))`. Establish `hW : (W : Set (KG K n)) = (fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n)) ⁻¹' O`. Use extensionality with `k`. Conclude with `⟨fun h => ((hUO k).1 h).1, fun h => (hUO k).2 ⟨h, k.2⟩⟩`.

Rewrite using `[hW]`. Conclude with `hO.preimage (continuous_subtype_val.comp continuous_subtype_val)`. Use `haveI : Finite (KG K n ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo`. Set `B` to `Module.finBasis ℂ 𝒜`. Set `x : G1 K n → 𝒜` to `fun m => ⟨fun u : D.U => f (m * u), hA f hf hfix m⟩`.

Set `c : Fin (Module.finrank ℂ 𝒜) × (KG K n ⧸ W) → G1 K n → ℂ` to `fun p m => B.repr (x (m * ((Quotient.out p.2 : KG K n) : G1 K n))) p.1`. Establish `hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c))` using `FiniteDimensional.span_of_finite ℂ (Set.finite_range c)`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul W k`.

Use `set q : KG K n ⧸ W := (k : KG K n ⧸ W) with hq`. Set `u : D.U` to `⟨(((h : KG K n)⁻¹ : KG K n) : G1 K n), Subgroup.mem_subgroupOf.1 (W.inv_mem h.2)⟩`. Establish `hk : (k : G1 K n) = ((Quotient.out q : KG K n) : G1 K n) * u`. Establish `: k = Quotient.out q * (h : KG K n)⁻¹`. Rewrite using `[hh]`.

Simplify using the standard rewrite rules. Conclude with `congrArg Subtype.val this`. Establish `e : (fun m => f (m * k)) = ∑ i, ((B i : 𝒜) : D.U → ℂ) u • c (i, q)`. Use function extensionality and compare the values at `m`. Establish `h1` using `congrArg (fun y : 𝒜 => (y : D.U → ℂ) u) (B.sum_repr (x (m * ((Quotient.out q : KG K n) : G1 K n))))`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hk, ← mul_assoc]`. Express the relevant statement in the definitionally equal form `_ = ∑ i, ((B i : 𝒜) : D.U → ℂ) u * B.repr (x (m * ((Quotient.out q : KG K n) : G1 K n))) i`. Simplify using `only [mul_comm (((B _ : 𝒜) : D.U → ℂ) u)]`.

Conclude with `h1.symm`. Express the relevant statement in the definitionally equal form `(fun m => f (m * (k : G1 K n))) ∈ Submodule.span ℂ (Set.range c)`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, q), rfl⟩)`.
-/
theorem UpperTheory.finiteDimensional_span_maximalCompact_translates_of_fix :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (f : G1 K n → ℂ), Continuous f → D.Fix f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K n => fun m => f (m * k))) := by
  intro K _ _ n D f hf hfix
  obtain ⟨-, -, 𝒜, hfd, -, hA⟩ := typeFin D
  haveI := hfd
  obtain ⟨O, hO, hUO⟩ := D.isOpen
  haveI : CompactSpace (KG K n) :=
    isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1
  let W : Subgroup (KG K n) := D.U.subgroupOf (KG K n)
  have hWo : IsOpen (W : Set (KG K n)) := by
    have hW : (W : Set (KG K n)) = (fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n)) ⁻¹' O := by
      ext k
      exact ⟨fun h => ((hUO k).1 h).1, fun h => (hUO k).2 ⟨h, k.2⟩⟩
    rw [hW]
    exact hO.preimage (continuous_subtype_val.comp continuous_subtype_val)
  haveI : Finite (KG K n ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo
  let B := Module.finBasis ℂ 𝒜
  let x : G1 K n → 𝒜 := fun m => ⟨fun u : D.U => f (m * u), hA f hf hfix m⟩
  let c : Fin (Module.finrank ℂ 𝒜) × (KG K n ⧸ W) → G1 K n → ℂ :=
    fun p m => B.repr (x (m * ((Quotient.out p.2 : KG K n) : G1 K n))) p.1
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul W k
  set q : KG K n ⧸ W := (k : KG K n ⧸ W) with hq
  let u : D.U := ⟨(((h : KG K n)⁻¹ : KG K n) : G1 K n), Subgroup.mem_subgroupOf.1 (W.inv_mem h.2)⟩
  have hk : (k : G1 K n) = ((Quotient.out q : KG K n) : G1 K n) * u := by
    have : k = Quotient.out q * (h : KG K n)⁻¹ := by
      rw [hh]; simp
    exact congrArg Subtype.val this
  have e : (fun m => f (m * k)) = ∑ i, ((B i : 𝒜) : D.U → ℂ) u • c (i, q) := by
    funext m
    have h1 := congrArg (fun y : 𝒜 => (y : D.U → ℂ) u)
      (B.sum_repr (x (m * ((Quotient.out q : KG K n) : G1 K n))))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk, ← mul_assoc]
    change _ = ∑ i, ((B i : 𝒜) : D.U → ℂ) u * B.repr (x (m * ((Quotient.out q : KG K n) : G1 K n))) i
    simp only [mul_comm (((B _ : 𝒜) : D.U → ℂ) u)]
    exact h1.symm
  change (fun m => f (m * (k : G1 K n))) ∈ Submodule.span ℂ (Set.range c)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, q), rfl⟩)
