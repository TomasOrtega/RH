import Formalism.AdmissibleDesigns.TensSubsingleton
import Formalism.AdmissibleDesigns.InvariantsEqBotIff
import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Font

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct Formalism.MainNotions.N.K.TBa

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

/- English proof (translation)
Establish `hs : ∀ b, Subsingleton ↥(FildR PD ρ τ b)` using `fun b => ⟨fun x y => Subtype.ext ((tens_subsingleton (x : V ⊗[Qp] BdR)).trans (tens_subsingleton (y : V ⊗[Qp] BdR)).symm)⟩`. Unfold `multV`. Use `haveI := hs a`. Use `haveI := hs (a + 1)`. Rewrite using `[Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]`.

Both sides reduce to the same expression.
-/
theorem multV_zero_of_subsingleton {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] [Subsingleton V] (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = 0 := by
  have hs : ∀ b, Subsingleton ↥(FildR PD ρ τ b) := fun b =>
    ⟨fun x y => Subtype.ext ((tens_subsingleton (x : V ⊗[Qp] BdR)).trans (tens_subsingleton (y : V ⊗[Qp] BdR)).symm)⟩
  unfold multV
  haveI := hs a
  haveI := hs (a + 1)
  rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
  rfl

variable {ι : Type} {k : ℕ} (Ms : ι → G →* Matrix (Fin k) (Fin k) LL)
  (hF : TruncatedSeriesCountingIdentities.FontaineAt PD LL O) (hMc : ∀ x, Continuous (Ms x))
include hF hMc

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `xs _ _ τ a _`. Use `haveI : Subsingleton (Fin 0 → Fin k → LL) := inferInstance`.

Conclude with `multV_zero_of_subsingleton PD _ τ a`. Consider the case `succ m ih`. Introduce `xs hc hJ τ a ha`. Set `A₀ : GRep G Qp LL O` to `sumG Ms hMc (fun a => xs a.succ)`. Set `A₁ : GRep G Qp LL O` to `sumG Ms hMc xs`.

Set `A₂ : GRep G Qp LL O` to `matG Ms hMc (xs 0)`. Set `ι₀ : A₀.V →ₗ[LL] A₁.V` to `consZ (W := Fin k → LL) m`. Set `π₀ : A₁.V →ₗ[LL] A₂.V` to `LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0`. Set `σ₀ : A₂.V →ₗ[LL] A₁.V` to `consV (W := Fin k → LL) m`. Establish `e1 : ∀ g x, ι₀ (A₀.ρ g x) = A₁.ρ g (ι₀ x)` using `fun g x => funext fun a => by`.

Consider the cases of `a using Fin.cases`. Use `show (0 : Fin k → LL) = (Ms (xs 0) g).mulVec 0`. Rewrite using `[Matrix.mulVec_zero]`. Both sides reduce to the same expression. Establish `e2 : ∀ g x, π₀ (A₁.ρ g x) = A₂.ρ g (π₀ x)` using `fun g x => rfl`.

Establish `hinj : Function.Injective ι₀` using `consZ_inj (W := Fin k → LL) m`. Establish `hsurj : Function.Surjective π₀` using `fun v => ⟨σ₀ v, proj_consV (W := Fin k → LL) m v⟩`. Establish `hex : LinearMap.range ι₀ = LinearMap.ker π₀` using `range_consZ (W := Fin k → LL) m`. Establish `hF1` using `hF.1 A₀ A₁ A₂ ι₀ π₀ e1 e2 hinj hsurj hex`. Take `⟨hc0, hc2, hadd⟩` from `hF1.1 hc`.

Establish `h0 : multV PD A₀.ρ τ a = 0` using `ih (fun a => xs a.succ) hc0 (fun j => hJ j.succ) τ a ha`. Establish `h2 : multV PD A₂.ρ τ a = 0`. Assume the negation of the conclusion as `hne`. Use `hJ 0 τ a (jump_of_mult PD _ τ a hne)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `show multV PD A₁.ρ τ a = 0`. Rewrite using `[hadd τ a, h0, h2, add_zero]`.
-/
theorem mult_sum_neg : ∀ (m : ℕ) (xs : Fin m → ι), IsCrys PD (sumRep Ms xs) →
    (∀ (j : Fin m) (τ : K →ₐ[Qp] LL) (b : ℤ), IsJumpV PD (matRep (Ms (xs j))) τ b → 0 ≤ b) →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), a < 0 → multV PD (sumRep Ms xs) τ a = 0 := by
  intro m
  induction m with
  | zero =>
    intro xs _ _ τ a _
    haveI : Subsingleton (Fin 0 → Fin k → LL) := inferInstance
    exact multV_zero_of_subsingleton PD _ τ a
  | succ m ih =>
    intro xs hc hJ τ a ha
    let A₀ : GRep G Qp LL O := sumG Ms hMc (fun a => xs a.succ)
    let A₁ : GRep G Qp LL O := sumG Ms hMc xs
    let A₂ : GRep G Qp LL O := matG Ms hMc (xs 0)
    let ι₀ : A₀.V →ₗ[LL] A₁.V := consZ (W := Fin k → LL) m
    let π₀ : A₁.V →ₗ[LL] A₂.V := LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0
    let σ₀ : A₂.V →ₗ[LL] A₁.V := consV (W := Fin k → LL) m
    have e1 : ∀ g x, ι₀ (A₀.ρ g x) = A₁.ρ g (ι₀ x) := fun g x => funext fun a => by
      cases a using Fin.cases
      · show (0 : Fin k → LL) = (Ms (xs 0) g).mulVec 0
        rw [Matrix.mulVec_zero]
      · rfl
    have e2 : ∀ g x, π₀ (A₁.ρ g x) = A₂.ρ g (π₀ x) := fun g x => rfl
    have hinj : Function.Injective ι₀ := consZ_inj (W := Fin k → LL) m
    have hsurj : Function.Surjective π₀ := fun v => ⟨σ₀ v, proj_consV (W := Fin k → LL) m v⟩
    have hex : LinearMap.range ι₀ = LinearMap.ker π₀ := range_consZ (W := Fin k → LL) m
    have hF1 := hF.1 A₀ A₁ A₂ ι₀ π₀ e1 e2 hinj hsurj hex
    obtain ⟨hc0, hc2, hadd⟩ := hF1.1 hc
    have h0 : multV PD A₀.ρ τ a = 0 :=
      ih (fun a => xs a.succ) hc0 (fun j => hJ j.succ) τ a ha
    have h2 : multV PD A₂.ρ τ a = 0 := by
      by_contra hne
      have := hJ 0 τ a (jump_of_mult PD _ τ a hne)
      omega
    show multV PD A₁.ρ τ a = 0
    rw [hadd τ a, h0, h2, add_zero]

/- English proof (translation)
Set `A₂ : GRep G Qp LL O` to `sumG Ms hMc xs`. Set `ι₀ : A₀.V →ₗ[LL] A₁.V` to `e.symm.toLinearMap ∘ₗ LinearMap.inl LL A₀.V (Fin m → Fin k → LL)`. Set `π₀ : A₁.V →ₗ[LL] A₂.V` to `LinearMap.snd LL A₀.V (Fin m → Fin k → LL) ∘ₗ e.toLinearMap`. Establish `e1 : ∀ g x, ι₀ (A₀.ρ g x) = A₁.ρ g (ι₀ x)`. Introduce `g x`.

Apply `e.injective` to reduce the goal to its premises. Use `show e (e.symm (A₀.ρ g x, 0)) = e (A₁.ρ g (e.symm (x, 0)))`. Rewrite using `[he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_zero]`. Establish `e2 : ∀ g x, π₀ (A₁.ρ g x) = A₂.ρ g (π₀ x)`. Introduce `g x`.

Use `show (e (A₁.ρ g x)).2 = sumRep Ms xs g (e x).2`. Rewrite using `[he]`. Establish `hinj : Function.Injective ι₀`. Introduce `x y h`. Establish `h' : e.symm (x, 0) = e.symm (y, 0)` using `h`.

Use `congrArg Prod.fst (e.symm.injective h')` as an intermediate fact. Conclude with `this`. Establish `hsurj : Function.Surjective π₀`. Introduce `y`. Use `⟨e.symm (0, y), ?_⟩` and prove the remaining obligations.

Use `show (e (e.symm (0, y))).2 = y`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Establish `hex : LinearMap.range ι₀ = LinearMap.ker π₀`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩ show (e (e.symm (x, 0))).2 = 0`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Introduce `hv`. Establish `hv' : (e v).2 = 0` using `hv`. Use `⟨(e v).1, ?_⟩` and prove the remaining obligations.

Use `show e.symm ((e v).1, 0) = v`. Rewrite using `[← hv']`. Conclude with `e.symm_apply_apply v`. Establish `hF1` using `hF.1 A₀ A₁ A₂ ι₀ π₀ e1 e2 hinj hsurj hex`. Take `⟨hc0, hc2, hadd⟩` from `hF1.1 hc`.

Use `⟨hc0, fun τ a ha => ?_⟩` and prove the remaining obligations. Establish `h2 : multV PD A₂.ρ τ a = 0` using `mult_sum_neg PD Ms hF hMc m xs hc2 hJ τ a ha`. Rewrite using `[hadd τ a, h2, add_zero]`.
-/
theorem decomp_neg (A₁ A₀ : GRep G Qp LL O) {m : ℕ} (xs : Fin m → ι)
    (e : A₁.V ≃ₗ[LL] A₀.V × (Fin m → Fin k → LL))
    (he : ∀ g v, e (A₁.ρ g v) = (A₀.ρ g (e v).1, sumRep Ms xs g (e v).2))
    (hc : IsCrys PD A₁.ρ)
    (hJ : ∀ (j : Fin m) (τ : K →ₐ[Qp] LL) (b : ℤ), IsJumpV PD (matRep (Ms (xs j))) τ b → 0 ≤ b) :
    IsCrys PD A₀.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), a < 0 → multV PD A₁.ρ τ a = multV PD A₀.ρ τ a := by
  let A₂ : GRep G Qp LL O := sumG Ms hMc xs
  let ι₀ : A₀.V →ₗ[LL] A₁.V := e.symm.toLinearMap ∘ₗ LinearMap.inl LL A₀.V (Fin m → Fin k → LL)
  let π₀ : A₁.V →ₗ[LL] A₂.V := LinearMap.snd LL A₀.V (Fin m → Fin k → LL) ∘ₗ e.toLinearMap
  have e1 : ∀ g x, ι₀ (A₀.ρ g x) = A₁.ρ g (ι₀ x) := by
    intro g x
    apply e.injective
    show e (e.symm (A₀.ρ g x, 0)) = e (A₁.ρ g (e.symm (x, 0)))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_zero]
  have e2 : ∀ g x, π₀ (A₁.ρ g x) = A₂.ρ g (π₀ x) := by
    intro g x
    show (e (A₁.ρ g x)).2 = sumRep Ms xs g (e x).2
    rw [he]
  have hinj : Function.Injective ι₀ := by
    intro x y h
    have h' : e.symm (x, 0) = e.symm (y, 0) := h
    have := congrArg Prod.fst (e.symm.injective h')
    exact this
  have hsurj : Function.Surjective π₀ := by
    intro y
    refine ⟨e.symm (0, y), ?_⟩
    show (e (e.symm (0, y))).2 = y
    rw [LinearEquiv.apply_symm_apply]
  have hex : LinearMap.range ι₀ = LinearMap.ker π₀ := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      show (e (e.symm (x, 0))).2 = 0
      rw [LinearEquiv.apply_symm_apply]
    · intro hv
      have hv' : (e v).2 = 0 := hv
      refine ⟨(e v).1, ?_⟩
      show e.symm ((e v).1, 0) = v
      rw [← hv']
      exact e.symm_apply_apply v
  have hF1 := hF.1 A₀ A₁ A₂ ι₀ π₀ e1 e2 hinj hsurj hex
  obtain ⟨hc0, hc2, hadd⟩ := hF1.1 hc
  refine ⟨hc0, fun τ a ha => ?_⟩
  have h2 : multV PD A₂.ρ τ a = 0 := mult_sum_neg PD Ms hF hMc m xs hc2 hJ τ a ha
  rw [hadd τ a, h2, add_zero]

end Gen

section GenNT

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

section DR

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

/- English proof (translation)
Set `E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR` to `AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)`. Establish `hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x)`. Introduce `g x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp [E, actVdR, he]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]`. Establish `hD : DdR PD ρ = (DdR PD ρ').comap (E : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR)`. Use extensionality with `x`. Simplify using `only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx g`. Rewrite using `[LinearEquiv.coe_coe, ← hE, hx g]`. Introduce `hx g`. Apply `E.injective` to reduce the goal to its premises.

Rewrite using `[hE]`. Conclude with `hx g`. Unfold `IsDR at h ⊢`. Rewrite using `[← e.finrank_eq, ← h, hD]`. Conclude with `(E.ofSubmodule' (DdR PD ρ')).finrank_eq.symm`.
-/
theorem isDR_congr (h : IsDR PD ρ) : IsDR PD ρ' := by
  let E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hD : DdR PD ρ = (DdR PD ρ').comap (E : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR) := by
    ext x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  unfold IsDR at h ⊢
  rw [← e.finrank_eq, ← h, hD]
  exact (E.ofSubmodule' (DdR PD ρ')).finrank_eq.symm

end DR

section MatT

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] {k : ℕ}
  (M : G →* Matrix (Fin k) (Fin k) LL) (ρ' : Representation LL G V) (e : V ≃ₗ[LL] (Fin k → LL))
  (he : ∀ g x, e (ρ' g x) = matRep M g (e x))
include he

/- English proof (translation)
Use `Norm.isCrys_congr PD e.symm (fun g y => ?_) h` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]`.
-/
theorem crys_of_mat (h : IsCrys PD (matRep M)) : IsCrys PD ρ' := by
  refine Norm.isCrys_congr PD e.symm (fun g y => ?_) h
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

/- English proof (translation)
The claim follows from `Norm.multV_congr PD e he τ a`.
-/
theorem multV_mat (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ' τ a = multV PD (matRep M) τ a :=
  Norm.multV_congr PD e he τ a

/- English proof (translation)
Use `isDR_congr PD e.symm (fun g y => ?_) h` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]`.
-/
theorem dR_of_mat (h : IsDR PD (matRep M)) : IsDR PD ρ' := by
  refine isDR_congr PD e.symm (fun g y => ?_) h
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

end MatT

end GenNT

end Formalism.MainNotions.N.K.Font

end
