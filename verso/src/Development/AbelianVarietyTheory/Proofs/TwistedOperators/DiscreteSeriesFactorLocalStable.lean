import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

noncomputable section

namespace GlobalTheory.PureDS

open GlobalTheory.AutMult

section Comb

variable {α β ι : Type} {Hs : α ⊕ β → Type} {E : ι → Type}

open Classical in

def comb (p : ι → α) (A : ∀ i, E i → Hs (.inl (p i))) (y0 : ∀ v, Hs v) (z : ∀ i, E i) : ∀ v, Hs v
  | .inl a => if h : ∃ i, p i = a then cast (congrArg (fun a => Hs (.inl a)) h.choose_spec) (A h.choose (z h.choose))
      else y0 (.inl a)
  | .inr b => y0 (.inr b)

variable {p : ι → α} {A : ∀ i, E i → Hs (.inl (p i))} {y0 : ∀ v, Hs v} {z : ∀ i, E i}

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_apply_eq {i j : ι} (e : p i = p j) (h : i = j) :
    cast (congrArg (fun a => Hs (.inl a)) e) (A i (z i)) = A j (z j) := by
  subst h; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem comb_inr (b : β) : comb p A y0 z (.inr b) = y0 (.inr b) := rfl

/- English proof (translation)
Establish `h : ∃ j, p j = p i` using `⟨i, rfl⟩`. Simplify using `only [comb, dif_pos h]`. Conclude with `cast_apply_eq h.choose_spec (hp h.choose_spec)`.
-/
theorem comb_inl (hp : Function.Injective p) (i : ι) : comb p A y0 z (.inl (p i)) = A i (z i) := by
  have h : ∃ j, p j = p i := ⟨i, rfl⟩
  simp only [comb, dif_pos h]
  exact cast_apply_eq h.choose_spec (hp h.choose_spec)

/- English proof (translation)
Simplify using `only [comb, dif_neg h]`.
-/
theorem comb_inl_of_not (a : α) (h : ¬ ∃ i, p i = a) : comb p A y0 z (.inl a) = y0 (.inl a) := by
  simp only [comb, dif_neg h]

/- English proof (translation)
Use function extensionality and compare the values at `v`. Break down `v with a | b` into its components or cases. Distinguish the cases in `h : ∃ j, p j = a`. Take `⟨j, rfl⟩` from `h`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Rewrite using `[comb_inl hp, Function.update_self, Function.update_self]`. Establish `hne : (Sum.inl (p j) : α ⊕ β) ≠ .inl (p i)` using `fun e => hj (hp (Sum.inl_injective e))`. Rewrite using `[comb_inl hp, Function.update_of_ne hne, comb_inl hp, Function.update_of_ne hj]`. Establish `hne : (Sum.inl a : α ⊕ β) ≠ .inl (p i)` using `fun e => h ⟨i, (Sum.inl_injective e).symm⟩`.

Rewrite using `[comb_inl_of_not a h, Function.update_of_ne hne, comb_inl_of_not a h]`. Rewrite using `[Function.update_of_ne Sum.inr_ne_inl]`. Both sides reduce to the same expression.
-/
theorem comb_update [DecidableEq ι] [DecidableEq (α ⊕ β)] (hp : Function.Injective p) (i : ι) (x : E i) :
    comb p A y0 (Function.update z i x) = Function.update (comb p A y0 z) (.inl (p i)) (A i x) := by
  funext v
  rcases v with a | b
  · by_cases h : ∃ j, p j = a
    · obtain ⟨j, rfl⟩ := h
      by_cases hj : j = i
      · subst hj
        rw [comb_inl hp, Function.update_self, Function.update_self]
      · have hne : (Sum.inl (p j) : α ⊕ β) ≠ .inl (p i) := fun e => hj (hp (Sum.inl_injective e))
        rw [comb_inl hp, Function.update_of_ne hne, comb_inl hp, Function.update_of_ne hj]
    · have hne : (Sum.inl a : α ⊕ β) ≠ .inl (p i) := fun e => h ⟨i, (Sum.inl_injective e).symm⟩
      rw [comb_inl_of_not a h, Function.update_of_ne hne, comb_inl_of_not a h]
  · rw [Function.update_of_ne Sum.inr_ne_inl]
    rfl

/- English proof (translation)
Use function extensionality and compare the values at `v`. Break down `v with a | b` into its components or cases. Take `⟨i, rfl⟩` from `hp.2 a`. Rewrite using `[comb_inl hp.1, hA]`. Conclude with `hy b`.
-/
theorem comb_eq_self (hp : Function.Bijective p) (Ainv : ∀ i, Hs (.inl (p i)) → E i) (hA : ∀ i x, A i (Ainv i x) = x)
    {y : ∀ v, Hs v} (hy : ∀ b, y0 (.inr b) = y (.inr b)) : comb p A y0 (fun i => Ainv i (y (.inl (p i)))) = y := by
  funext v
  rcases v with a | b
  · obtain ⟨i, rfl⟩ := hp.2 a
    rw [comb_inl hp.1, hA]
  · exact hy b

/- English proof (translation)
Use `(Set.Finite.union h ((Set.finite_range p).image Sum.inl)).subset fun v hv => ?_` and prove the remaining obligations. Break down `v with a | b` into its components or cases. Distinguish the cases in `ha : ∃ i, p i = a`. Take `⟨i, rfl⟩` from `ha`. Conclude with `Or.inr ⟨p i, ⟨i, rfl⟩, rfl⟩`.

Use `Or.inl ?_` and prove the remaining obligations. Establish `hv' : comb p A y0 z (.inl a) ≠ ξ (.inl a)` using `hv`. Rewrite `hv'` using `[comb_inl_of_not a ha]`. Then use the resulting hypothesis. Conclude with `Or.inl hv`.
-/
theorem restr_comb [Finite ι] {ξ : ∀ v, Hs v} (h : Restr ξ y0) : Restr ξ (comb p A y0 z) := by
  refine (Set.Finite.union h ((Set.finite_range p).image Sum.inl)).subset fun v hv => ?_
  rcases v with a | b
  · by_cases ha : ∃ i, p i = a
    · obtain ⟨i, rfl⟩ := ha
      exact Or.inr ⟨p i, ⟨i, rfl⟩, rfl⟩
    · refine Or.inl ?_
      have hv' : comb p A y0 z (.inl a) ≠ ξ (.inl a) := hv
      rwa [comb_inl_of_not a ha] at hv'
  · exact Or.inl hv

end Comb

section Abstract

variable {ι G K κ : Type} {Γ Hs : ι → Type} [Fintype ι] [DecidableEq ι] [Group G] [∀ i, Group (Γ i)]
  [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [TopologicalSpace G] [∀ i, TopologicalSpace (Γ i)]
  {e : ∀ i, Γ i →* G} {δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)} {ρ : G →* (K →L[ℂ] K)}

/- English proof (translation)
Set `L : homPi e δ ρ X →ₗ[ℂ] (κ → ℂ)` to `{ toFun := fun Φ k => bePi Φ.1 (Ψ k) map_add' := fun Φ Φ' => funext fun k => by simp [bePi, inner_add_right] map_smul' := fun c Φ => funext fun k => by simp [bePi, inner_smul_right] }`. Use `Module.Finite.of_injective L ((injective_iff_map_eq_zero L).2 fun Φ hΦ => ?_)` and prove the remaining obligations. Use `Subtype.ext (ContinuousMultilinearMap.ext fun y => ?_)` and prove the remaining obligations. Establish `hle : (Submodule.span ℂ {v | ∃ k y, v = Ψ k y}).topologicalClosure ≤ (ℂ ∙ Φ.1 y)ᗮ` using `Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨k, z, rfl⟩`.

Use `Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_` and prove the remaining obligations. Rewrite using `[inner_eq_bePi hδ hρ Φ.2 (hΨ k) y z]`. Establish `: bePi Φ.1 (Ψ k) = 0` using `congrFun hΦ k`. Rewrite using `[this, zero_mul])) (Submodule.isClosed_orthogonal _)`. Use `Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle (hX (Φ.2.1 y)))` as an intermediate fact.

Simplify using `using inner_self_eq_zero.1 this`.
-/
theorem finiteDimensional_homPi_of_le [Finite κ] (hδ : ∀ i, IsIrrUnitary (δ i)) (hρ : IsUnitaryRep ρ)
    (Ψ : κ → ContinuousMultilinearMap ℂ Hs K) (hΨ : ∀ k, Ψ k ∈ homPi e δ ρ ⊤) {X : Submodule ℂ K}
    (hX : X ≤ (Submodule.span ℂ {v | ∃ k y, v = Ψ k y}).topologicalClosure) :
    FiniteDimensional ℂ (homPi e δ ρ X) := by
  let L : homPi e δ ρ X →ₗ[ℂ] (κ → ℂ) :=
    { toFun := fun Φ k => bePi Φ.1 (Ψ k)
      map_add' := fun Φ Φ' => funext fun k => by simp [bePi, inner_add_right]
      map_smul' := fun c Φ => funext fun k => by simp [bePi, inner_smul_right] }
  refine Module.Finite.of_injective L ((injective_iff_map_eq_zero L).2 fun Φ hΦ => ?_)
  refine Subtype.ext (ContinuousMultilinearMap.ext fun y => ?_)
  have hle : (Submodule.span ℂ {v | ∃ k y, v = Ψ k y}).topologicalClosure ≤ (ℂ ∙ Φ.1 y)ᗮ :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (by
      rintro _ ⟨k, z, rfl⟩
      refine Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_
      rw [inner_eq_bePi hδ hρ Φ.2 (hΨ k) y z]
      have : bePi Φ.1 (Ψ k) = 0 := congrFun hΦ k
      rw [this, zero_mul])) (Submodule.isClosed_orthogonal _)
  have := Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle (hX (Φ.2.1 y)))
  simpa using inner_self_eq_zero.1 this

end Abstract

section Act

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Hs : Formalism.MainNotions.SchurIrreducible.Pl F → Type} [∀ v, NormedAddCommGroup (Hs v)] [∀ v, InnerProductSpace ℂ (Hs v)]
  {δ : ∀ v, GPl σ J v →* (Hs v →L[ℂ] Hs v)} {ξ : ∀ v, Hs v} {π : GAd σ J →* (H →L[ℂ] H)} {B : (∀ v, Hs v) → H}
  {ι : Type} {Eτ : ι → Type} [∀ i, NormedAddCommGroup (Eτ i)] [∀ i, InnerProductSpace ℂ (Eτ i)]

/- English proof (translation)
Rewrite using `[comb_update hp, hA, ← comb_inl (A := A) (y0 := y0) (z := z) hp i]`. Conclude with `(hB.apply_embPl (restr_comb hy0) (.inl (p i)) g).symm`.
-/
theorem apply_embArch_comb [Finite ι] [DecidableEq ι] [DecidableEq (Formalism.MainNotions.SchurIrreducible.Pl F)]
    (hB : IsFactorisation σ J δ ξ π B) {p : ι → InfinitePlace F} (hp : Function.Injective p)
    (ρ : ∀ i, GArch σ J (p i) →* (Eτ i →L[ℂ] Eτ i)) (A : ∀ i, Eτ i → Hs (.inl (p i)))
    (hA : ∀ i g x, A i (ρ i g x) = δ (.inl (p i)) g (A i x)) {y0 : ∀ v, Hs v} (hy0 : Restr ξ y0)
    (z : ∀ i, Eτ i) (i : ι) (g : GArch σ J (p i)) :
    B (comb p A y0 (Function.update z i (ρ i g (z i)))) = π (embArch σ J (p i) g) (B (comb p A y0 z)) := by
  rw [comb_update hp, hA, ← comb_inl (A := A) (y0 := y0) (z := z) hp i]
  exact (hB.apply_embPl (restr_comb hy0) (.inl (p i)) g).symm

end Act

end GlobalTheory.PureDS

namespace GlobalTheory.PureDS

open GlobalTheory.AutMult

section Expand

/- English proof (translation)
Proceed by induction on `T, hT using Set.Finite.induction_on generalizing y with`. Consider the case `empty => exact Submodule.subset_span ⟨y, fun _ _ => rfl, fun i hi => absurd hi (Set.notMem_empty i), rfl⟩`. Consider the case `@insert i T hi hT ih`. Establish `h0 : B (Function.update y i 0) = 0`. Use `hB y hy i 1 0 0` as an intermediate fact.

Simplify using `only [one_smul, add_zero] at this`. Simplify using `using this`. Set `L : N i →ₗ[ℂ] K` to `{ toFun := fun x => B (Function.update y i x) map_add' := fun a c => by simpa using hB y hy i 1 a c map_smul' := fun c a => by simpa [h0] using hB y hy i c a 0 }`. Establish `hy' : B y = L (y i)` using `by simp [L]`. Rewrite using `[hy']`.

Use `Submodule.span_le.2 ?_ (Submodule.apply_mem_span_image_of_mem_span L (hyT i (Set.mem_insert i T)))` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `ih (y := Function.update y i x) (GlobalTheory.SmallThetaModules.restr_update hy i x) fun j hj => by` as an intermediate fact. Rewrite using `[Function.update_of_ne (by rintro rfl; exact hi hj)]`. Conclude with `hyT j (Set.mem_insert_of_mem i hj)`.

Use `Submodule.span_mono ?_ this` and prove the remaining obligations. Introduce and unpack `_ ⟨y', hoff, hon, rfl⟩`. Use `⟨y', fun j hj => ?_, fun j hj => ?_, rfl⟩` and prove the remaining obligations. Establish `hji : j ≠ i` using `fun e => hj (e ▸ Set.mem_insert i T)`. Rewrite using `[hoff j (fun h => hj (Set.mem_insert_of_mem i h)), Function.update_of_ne hji]`.

Break down `hj with rfl | hj` into its components or cases. Rewrite using `[hoff j hi, Function.update_self]`. Conclude with `hx`. Conclude with `hon j hj`.
-/
theorem mem_span_of_mem_span {ι K : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    [DecidableEq ι] [AddCommGroup K] [Module ℂ K] {ξ : ∀ i, N i} {B : (∀ i, N i) → K}
    (hB : ∀ y, Restr ξ y → ∀ i (c : ℂ) (a b : N i),
      B (Function.update y i (c • a + b)) = c • B (Function.update y i a) + B (Function.update y i b))
    (b : ∀ i, Set (N i)) {T : Set ι} (hT : T.Finite) {y : ∀ i, N i} (hy : Restr ξ y)
    (hyT : ∀ i ∈ T, y i ∈ Submodule.span ℂ (b i)) :
    B y ∈ Submodule.span ℂ {w | ∃ y', (∀ i, i ∉ T → y' i = y i) ∧ (∀ i ∈ T, y' i ∈ b i) ∧ w = B y'} := by
  induction T, hT using Set.Finite.induction_on generalizing y with
  | empty => exact Submodule.subset_span ⟨y, fun _ _ => rfl, fun i hi => absurd hi (Set.notMem_empty i), rfl⟩
  | @insert i T hi hT ih =>
    have h0 : B (Function.update y i 0) = 0 := by
      have := hB y hy i 1 0 0
      simp only [one_smul, add_zero] at this
      simpa using this
    let L : N i →ₗ[ℂ] K :=
      { toFun := fun x => B (Function.update y i x)
        map_add' := fun a c => by simpa using hB y hy i 1 a c
        map_smul' := fun c a => by simpa [h0] using hB y hy i c a 0 }
    have hy' : B y = L (y i) := by simp [L]
    rw [hy']
    refine Submodule.span_le.2 ?_ (Submodule.apply_mem_span_image_of_mem_span L (hyT i (Set.mem_insert i T)))
    rintro _ ⟨x, hx, rfl⟩
    have := ih (y := Function.update y i x) (GlobalTheory.SmallThetaModules.restr_update hy i x) fun j hj => by
      rw [Function.update_of_ne (by rintro rfl; exact hi hj)]
      exact hyT j (Set.mem_insert_of_mem i hj)
    refine Submodule.span_mono ?_ this
    rintro _ ⟨y', hoff, hon, rfl⟩
    refine ⟨y', fun j hj => ?_, fun j hj => ?_, rfl⟩
    · have hji : j ≠ i := fun e => hj (e ▸ Set.mem_insert i T)
      rw [hoff j (fun h => hj (Set.mem_insert_of_mem i h)), Function.update_of_ne hji]
    · rcases hj with rfl | hj
      · rw [hoff j hi, Function.update_self]
        exact hx
      · exact hon j hj

end Expand

section Main

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : GA D V →* (H →L[ℂ] H)} {R : ∀ v, IrrU (GPl D.sp.cm.sig V.gram v)}
  {ξ : ∀ v, (R v).H} {B : (∀ v, (R v).H) → H}

/- English proof (translation)
Use `haveI := hπ.complete`. Use `haveI := hπ.irred.1`. Conclude with `IsIsotypic.uEquiv (isIrrUnitary_dsRep M τ) (R _).isIrr (isUnitaryRep_comp hπ.unitary (continuous_embPl D.sp.cm.sig V.gram (.inl (placeOf D τ)))) (hds τ) (hB.hasCompPl _)`.
-/
theorem uEquiv_dsRep (hπ : IsIrrUnitary π) (hds : HasDSComp M π)
    (hB : IsFactorisation D.sp.cm.sig V.gram (fun v => (R v).π) ξ π B) (τ : D.what₂.Tau) :
    UEquiv (dsRep M τ) (R (.inl (placeOf D τ))).π := by
  haveI := hπ.complete
  haveI := hπ.irred.1
  exact IsIsotypic.uEquiv (isIrrUnitary_dsRep M τ) (R _).isIrr
    (isUnitaryRep_comp hπ.unitary (continuous_embPl D.sp.cm.sig V.gram (.inl (placeOf D τ)))) (hds τ)
    (hB.hasCompPl _)

/- English proof (translation)
Establish `hinj` using `(placeOf_bijective D).1`. Take `⟨c, hcdef⟩ : ∃ c : (∀ τ, M.H τ) → ∀ v, (R v).H, c = comb (Hs` from `fun v => (R v).H) (placeOf D) (fun τ => A τ) y0 := ⟨_, rfl⟩`. Establish `hc : ∀ z, Restr ξ (c z)` using `fun z => hcdef ▸ restr_comb hy0`. Establish `h0 : ∀ y, Restr ξ y → ∀ v, B (Function.update y v 0) = 0` using `fun y hy v => by`. Use `hB.pure_update hy v 1 0 0` as an intermediate fact.

Simplify using `only [one_smul, add_zero] at this`. Simplify using `using this`. Establish `key : ∀ y, Restr ξ y → ∀ v (a : (R v).H), ‖B (Function.update y v a)‖ ^ 2 = ‖a‖ ^ 2 * ‖∏ᶠ (u) (_ : u ≠ v), ⟪y u, y u⟫_ℂ‖`. Introduce `y hy v a`. Establish `e` using `hB.inner_update hy (GlobalTheory.SmallThetaModules.restr_update hy v a) v a`.

Rewrite using `[Function.update_self, finprod_congr fun u => finprod_congr fun hu : u ≠ v => by`. Rewrite `e` using `[Function.update_of_ne hu]]`. Establish `e'` using `congrArg norm e`. Rewrite `e'` using `[norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Simplify using `using e'`.

Establish `scale : ∀ y, Restr ξ y → ∀ v (a b : (R v).H), ‖B (Function.update y v a)‖ * ‖b‖ = ‖B (Function.update y v b)‖ * ‖a‖` using `fun y hy v a b => by`. Use `(pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[mul_pow, mul_pow, key y hy v a, key y hy v b]`. Expand and normalize the polynomial expressions, which then agree. Set `f : MultilinearMap ℂ M.H H` to `{ toFun := fun z => B (c z) map_update_add' := fun z τ x x' => by`.

Simplify using `only [hcdef, comb_update hinj, map_add]`. Establish `h` using `hB.pure_update (hc z) (.inl (placeOf D τ)) 1 (A τ x) (A τ x')`. Rewrite `h` using `[hcdef]`. Simplify using `using h`. Use the proof step `map_update_smul' := fun z τ a x => by`.

Simplify using `only [hcdef, comb_update hinj, map_smul]`. Establish `h` using `hB.pure_update (hc z) (.inl (placeOf D τ)) a (A τ x) 0`. Establish `h0'` using `h0 _ (hc z) (.inl (placeOf D τ))`. Rewrite `h`, `h0'` using `[hcdef]`. Simplify `h }` using `[h0']`.

Establish `hf : ∀ z, f z = B (c z)` using `fun z => rfl`. Set `u : ∀ τ, M.H τ` to `fun τ => unitVec (M.H τ)`. Establish `hu : ∀ τ, ‖u τ‖ = 1` using `fun τ => by haveI := (isIrrUnitary_dsRep M τ).irred.1`. Conclude with `norm_unitVec _`. Establish `hsc : ∀ z τ (x : M.H τ), ‖f (Function.update z τ x)‖ = ‖f (Function.update z τ (u τ))‖ * ‖x‖`.

Introduce `z τ x`. Use `scale (c z) (hc z) (.inl (placeOf D τ)) (A τ x) (A τ (u τ))` as an intermediate fact. Rewrite `this` using `[LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, hu, mul_one]`. Rewrite using `[hf, hf, hcdef, comb_update hinj, comb_update hinj, ← hcdef, this]`. Establish `hb : ∀ (s : Finset D.what₂.Tau) z, ‖f z‖ = ‖f (s.piecewise u z)‖ * ∏ τ ∈ s, ‖z τ‖`.

Introduce `s z`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert τ s hτ ih`. Rewrite using `[Finset.prod_insert hτ, Finset.piecewise_insert, ← mul_assoc, ih]`.

Use `congr 1`. Use `conv_lhs => rw [← Function.update_eq_self τ (s.piecewise u z)]`. Rewrite using `[hsc, s.piecewise_eq_of_notMem u z hτ]`. Use `⟨f.mkContinuous ‖f u‖ fun z => le_of_eq (by simpa using hb Finset.univ z), ?_, fun z => ?_⟩` and prove the remaining obligations. Use `show _ ∈ homPi _ _ _ _`.

Use `⟨fun _ => trivial, fun τ g z => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f _ = π _ (f z)`. Rewrite using `[hf, hf, hcdef]`. Conclude with `apply_embArch_comb hB hinj (dsRep M) (fun τ => A τ) hA hy0 z τ g`. Express the relevant statement in the definitionally equal form `f z = _`.

Rewrite using `[hf, hcdef]`.
-/
theorem exists_homDS_comb (hB : IsFactorisation D.sp.cm.sig V.gram (fun v => (R v).π) ξ π B)
    (A : ∀ τ, M.H τ ≃ₗᵢ[ℂ] (R (.inl (placeOf D τ))).H)
    (hA : ∀ τ g x, A τ (dsRep M τ g x) = (R (.inl (placeOf D τ))).π g (A τ x))
    (y0 : ∀ v, (R v).H) (hy0 : Restr ξ y0) :
    ∃ Ψ ∈ homDS M π ⊤, ∀ z, Ψ z = B (comb (Hs := fun v => (R v).H) (placeOf D) (fun τ => A τ) y0 z) := by
  classical
  have hinj := (placeOf_bijective D).1
  obtain ⟨c, hcdef⟩ : ∃ c : (∀ τ, M.H τ) → ∀ v, (R v).H,
      c = comb (Hs := fun v => (R v).H) (placeOf D) (fun τ => A τ) y0 := ⟨_, rfl⟩
  have hc : ∀ z, Restr ξ (c z) := fun z => hcdef ▸ restr_comb hy0
  have h0 : ∀ y, Restr ξ y → ∀ v, B (Function.update y v 0) = 0 := fun y hy v => by
    have := hB.pure_update hy v 1 0 0
    simp only [one_smul, add_zero] at this
    simpa using this
  have key : ∀ y, Restr ξ y → ∀ v (a : (R v).H),
      ‖B (Function.update y v a)‖ ^ 2 = ‖a‖ ^ 2 * ‖∏ᶠ (u) (_ : u ≠ v), ⟪y u, y u⟫_ℂ‖ := by
    intro y hy v a
    have e := hB.inner_update hy (GlobalTheory.SmallThetaModules.restr_update hy v a) v a
    rw [Function.update_self, finprod_congr fun u => finprod_congr fun hu : u ≠ v => by
      rw [Function.update_of_ne hu]] at e
    have e' := congrArg norm e
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e'
    simpa using e'
  have scale : ∀ y, Restr ξ y → ∀ v (a b : (R v).H),
      ‖B (Function.update y v a)‖ * ‖b‖ = ‖B (Function.update y v b)‖ * ‖a‖ := fun y hy v a b => by
    refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, mul_pow, key y hy v a, key y hy v b]
    ring
  let f : MultilinearMap ℂ M.H H :=
    { toFun := fun z => B (c z)
      map_update_add' := fun z τ x x' => by
        simp only [hcdef, comb_update hinj, map_add]
        have h := hB.pure_update (hc z) (.inl (placeOf D τ)) 1 (A τ x) (A τ x')
        rw [hcdef] at h
        simpa using h
      map_update_smul' := fun z τ a x => by
        simp only [hcdef, comb_update hinj, map_smul]
        have h := hB.pure_update (hc z) (.inl (placeOf D τ)) a (A τ x) 0
        have h0' := h0 _ (hc z) (.inl (placeOf D τ))
        rw [hcdef] at h h0'
        simpa [h0'] using h }
  have hf : ∀ z, f z = B (c z) := fun z => rfl
  let u : ∀ τ, M.H τ := fun τ => unitVec (M.H τ)
  have hu : ∀ τ, ‖u τ‖ = 1 := fun τ => by
    haveI := (isIrrUnitary_dsRep M τ).irred.1
    exact norm_unitVec _
  have hsc : ∀ z τ (x : M.H τ), ‖f (Function.update z τ x)‖ = ‖f (Function.update z τ (u τ))‖ * ‖x‖ := by
    intro z τ x
    have := scale (c z) (hc z) (.inl (placeOf D τ)) (A τ x) (A τ (u τ))
    rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, hu, mul_one] at this
    rw [hf, hf, hcdef, comb_update hinj, comb_update hinj, ← hcdef, this]
  have hb : ∀ (s : Finset D.what₂.Tau) z, ‖f z‖ = ‖f (s.piecewise u z)‖ * ∏ τ ∈ s, ‖z τ‖ := by
    intro s z
    induction s using Finset.induction_on with
    | empty => simp
    | insert τ s hτ ih =>
      rw [Finset.prod_insert hτ, Finset.piecewise_insert, ← mul_assoc, ih]
      congr 1
      conv_lhs => rw [← Function.update_eq_self τ (s.piecewise u z)]
      rw [hsc, s.piecewise_eq_of_notMem u z hτ]
  refine ⟨f.mkContinuous ‖f u‖ fun z => le_of_eq (by simpa using hb Finset.univ z), ?_, fun z => ?_⟩
  · show _ ∈ homPi _ _ _ _
    refine ⟨fun _ => trivial, fun τ g z => ?_⟩
    change f _ = π _ (f z)
    rw [hf, hf, hcdef]
    exact apply_embArch_comb hB hinj (dsRep M) (fun τ => A τ) hA hy0 z τ g
  · change f z = _
    rw [hf, hcdef]

/- English proof (translation)
Use `haveI := hπ.complete`. Use `choose A hA using fun τ => uEquiv_dsRep hπ hds hB τ`. Use `set Sb : Set (HeightOneSpectrum (𝓞 D.host.F)) := {v | ¬ Q v ≤ ℂ ∙ ξ (.inr v)} with hSb`. Establish `hSbf : Sb.Finite` using `hQξ`. Use `haveI : Finite Sb := hSbf.to_subtype`.

Set `bas : ∀ v, Fin (Module.finrank ℂ (Q v)) → (R (.inr v)).H` to `fun v k => (Module.finBasis ℂ (Q v) k : _)`. Set `y0 : (∀ v : Sb, Fin (Module.finrank ℂ (Q v))) → ∀ v, (R v).H` to `fun k v => match v with`. Consider the case `.inl w => ξ (.inl w)`. Consider the case `.inr v => if h : v ∈ Sb then bas v (k ⟨v, h⟩) else ξ (.inr v)`. Establish `hy0 : ∀ k, Restr ξ (y0 k)` using `fun k => (hSbf.image Sum.inr).subset fun v hv => by`.

Break down `v with w | v` into its components or cases. Conclude with `absurd rfl hv`. Distinguish the cases in `h : v ∈ Sb`. Conclude with `⟨v, h, rfl⟩`. Conclude with `absurd (by simp [y0, h]) hv`.

Use `choose Ψ hΨ hΨB using fun k => exists_homDS_comb hB A hA (y0 k) (hy0 k)`. Use `finiteDimensional_homPi_of_le (fun τ => isIrrUnitary_dsRep M τ) hπ.unitary Ψ hΨ ?_` and prove the remaining obligations. Use `Submodule.topologicalClosure_mono (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, hyQ, rfl⟩`. Set `b : ∀ v, Set (R v).H` to `fun v => match v with`.

Consider the case `.inl _ => ∅`. Consider the case `.inr v => if v ∈ Sb then Set.range (bas v) else {ξ (.inr v)}`. Set `T : Set (Formalism.MainNotions.SchurIrreducible.Pl D.host.F)` to `Sum.inr '' (Sb ∪ {v | y (.inr v) ≠ ξ (.inr v)})`. Establish `hT : T.Finite` using `(hSbf.union (hy.preimage Sum.inr_injective.injOn)).image _`. Establish `hyT : ∀ v ∈ T, y v ∈ Submodule.span ℂ (b v)`.

Introduce and unpack `_ ⟨v, -, rfl⟩`. Distinguish the cases in `h : v ∈ Sb`. Simplify using `only [b, if_pos h]`. Establish `e : Set.range (bas v) = (Q v).subtype '' Set.range (Module.finBasis ℂ (Q v))`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[e, Submodule.span_image, (Module.finBasis ℂ (Q v)).span_eq, Submodule.map_top, Submodule.range_subtype]`. Conclude with `hyQ v`. Simplify using `only [b, if_neg h]`. Establish `: Q v ≤ ℂ ∙ ξ (.inr v)` using `not_not.1 h`.

Conclude with `this (hyQ v)`. Use `Submodule.span_le.2 ?_ (mem_span_of_mem_span (fun y hy => hB.pure_update hy) b hT hy hyT)` and prove the remaining obligations. Introduce and unpack `_ ⟨y', hy'off, hy'T, rfl⟩`. Establish `hk : ∀ v : Sb, ∃ j, y' (.inr v) = bas v j` using `fun v => by`. Use `hy'T (.inr v) ⟨v, Or.inl v.2, rfl⟩` as an intermediate fact.

Simplify using `only [b, if_pos v.2] at this`. Take `⟨j, hj⟩` from `this`. Conclude with `⟨j, hj.symm⟩`. Use `choose k hk using hk`. Establish `hagree : ∀ v, y0 k (.inr v) = y' (.inr v)` using `fun v => by`.

Distinguish the cases in `h : v ∈ Sb`. Simplify using `only [y0, dif_pos h]`. Conclude with `(hk ⟨v, h⟩).symm`. Simplify using `only [y0, dif_neg h]`. Distinguish the cases in `hv : y (.inr v) ≠ ξ (.inr v)`.

Use `hy'T (.inr v) ⟨v, Or.inr hv, rfl⟩` as an intermediate fact. Simplify using `only [b, if_neg h] at this`. Conclude with `this.symm`. Rewrite using `[hy'off (.inr v) (by rintro ⟨u, hu, e⟩; obtain rfl := Sum.inr_injective e; exact hu.elim h hv)]`. Conclude with `(not_not.1 hv).symm`.

Use `Submodule.subset_span ⟨k, fun τ => (A τ).symm (y' (.inl (placeOf D τ))), ?_⟩` and prove the remaining obligations. Rewrite using `[hΨB, comb_eq_self (placeOf_bijective D) (fun τ => (A τ).symm) (fun τ x => (A τ).apply_symm_apply x) hagree]`.
-/
theorem finiteDimensional_homDS_span (hπ : IsIrrUnitary π) (hds : HasDSComp M π)
    (hB : IsFactorisation D.sp.cm.sig V.gram (fun v => (R v).π) ξ π B)
    (Q : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Submodule ℂ (R (.inr v)).H) (hQ : ∀ v, FiniteDimensional ℂ (Q v))
    (hQξ : ∀ᶠ v in cofinite, Q v ≤ ℂ ∙ ξ (.inr v)) :
    FiniteDimensional ℂ (homDS M π
      (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ v, y (.inr v) ∈ Q v) ∧ z = B y}).topologicalClosure) := by
  classical
  haveI := hπ.complete
  choose A hA using fun τ => uEquiv_dsRep hπ hds hB τ
  set Sb : Set (HeightOneSpectrum (𝓞 D.host.F)) := {v | ¬ Q v ≤ ℂ ∙ ξ (.inr v)} with hSb
  have hSbf : Sb.Finite := hQξ
  haveI : Finite Sb := hSbf.to_subtype
  let bas : ∀ v, Fin (Module.finrank ℂ (Q v)) → (R (.inr v)).H := fun v k => (Module.finBasis ℂ (Q v) k : _)
  let y0 : (∀ v : Sb, Fin (Module.finrank ℂ (Q v))) → ∀ v, (R v).H := fun k v => match v with
    | .inl w => ξ (.inl w)
    | .inr v => if h : v ∈ Sb then bas v (k ⟨v, h⟩) else ξ (.inr v)
  have hy0 : ∀ k, Restr ξ (y0 k) := fun k => (hSbf.image Sum.inr).subset fun v hv => by
    rcases v with w | v
    · exact absurd rfl hv
    · by_cases h : v ∈ Sb
      · exact ⟨v, h, rfl⟩
      · exact absurd (by simp [y0, h]) hv
  choose Ψ hΨ hΨB using fun k => exists_homDS_comb hB A hA (y0 k) (hy0 k)
  refine finiteDimensional_homPi_of_le (fun τ => isIrrUnitary_dsRep M τ) hπ.unitary Ψ hΨ ?_
  refine Submodule.topologicalClosure_mono (Submodule.span_le.2 ?_)
  rintro _ ⟨y, hy, hyQ, rfl⟩
  let b : ∀ v, Set (R v).H := fun v => match v with
    | .inl _ => ∅
    | .inr v => if v ∈ Sb then Set.range (bas v) else {ξ (.inr v)}
  let T : Set (Formalism.MainNotions.SchurIrreducible.Pl D.host.F) := Sum.inr '' (Sb ∪ {v | y (.inr v) ≠ ξ (.inr v)})
  have hT : T.Finite := (hSbf.union (hy.preimage Sum.inr_injective.injOn)).image _
  have hyT : ∀ v ∈ T, y v ∈ Submodule.span ℂ (b v) := by
    rintro _ ⟨v, -, rfl⟩
    by_cases h : v ∈ Sb
    · simp only [b, if_pos h]
      have e : Set.range (bas v) = (Q v).subtype '' Set.range (Module.finBasis ℂ (Q v)) := by
        rw [← Set.range_comp]; rfl
      rw [e, Submodule.span_image, (Module.finBasis ℂ (Q v)).span_eq, Submodule.map_top, Submodule.range_subtype]
      exact hyQ v
    · simp only [b, if_neg h]
      have : Q v ≤ ℂ ∙ ξ (.inr v) := not_not.1 h
      exact this (hyQ v)
  refine Submodule.span_le.2 ?_ (mem_span_of_mem_span (fun y hy => hB.pure_update hy) b hT hy hyT)
  rintro _ ⟨y', hy'off, hy'T, rfl⟩
  have hk : ∀ v : Sb, ∃ j, y' (.inr v) = bas v j := fun v => by
    have := hy'T (.inr v) ⟨v, Or.inl v.2, rfl⟩
    simp only [b, if_pos v.2] at this
    obtain ⟨j, hj⟩ := this
    exact ⟨j, hj.symm⟩
  choose k hk using hk
  have hagree : ∀ v, y0 k (.inr v) = y' (.inr v) := fun v => by
    by_cases h : v ∈ Sb
    · simp only [y0, dif_pos h]
      exact (hk ⟨v, h⟩).symm
    · simp only [y0, dif_neg h]
      by_cases hv : y (.inr v) ≠ ξ (.inr v)
      · have := hy'T (.inr v) ⟨v, Or.inr hv, rfl⟩
        simp only [b, if_neg h] at this
        exact this.symm
      · rw [hy'off (.inr v) (by rintro ⟨u, hu, e⟩; obtain rfl := Sum.inr_injective e; exact hu.elim h hv)]
        exact (not_not.1 hv).symm
  refine Submodule.subset_span ⟨k, fun τ => (A τ).symm (y' (.inl (placeOf D τ))), ?_⟩
  rw [hΨB, comb_eq_self (placeOf_bijective D) (fun τ => (A τ).symm) (fun τ x => (A τ).apply_symm_apply x) hagree]

end Main

end GlobalTheory.PureDS

/- English proof (translation)
Introduce `D V S M H _ _ π hπ hds R ξ B hB Q hQ hQξ`. Conclude with `GlobalTheory.PureDS.finiteDimensional_homDS_span hπ hds hB Q hQ hQξ`.
-/
theorem GlobalTheory.PureDS.finiteDimensional_homDS_closure_span : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → HasDSComp M π → ∀ (R : ∀ v, IrrU (GPl D.sp.cm.sig V.gram v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), IsFactorisation D.sp.cm.sig V.gram (fun v => (R v).π) ξ π B → ∀ (Q : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Submodule ℂ (R (.inr v)).H), (∀ v, FiniteDimensional ℂ (Q v)) → (∀ᶠ v in cofinite, Q v ≤ ℂ ∙ ξ (.inr v)) → FiniteDimensional ℂ (homDS M π (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ v, y (.inr v) ∈ Q v) ∧ z = B y}).topologicalClosure) := by
  intro D V S M H _ _ π hπ hds R ξ B hB Q hQ hQξ
  exact GlobalTheory.PureDS.finiteDimensional_homDS_span hπ hds hB Q hQ hQξ
