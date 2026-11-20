import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.IrrInfChar

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k => exact commute_cap_finRep τ u k`. Consider the case `cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _`. Consider the case `lie X => exact commute_cap_lie τ u X`.
-/
theorem cap_commute_act' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (τ : E →+* ℂ) (u : ℂ)
    (o : Op E a) : Commute (cap (a := a) τ u) (act o) := by
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
  | lie X => exact commute_cap_lie τ u X

/- English proof (translation)
Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 hV.ne_bot`. Use `set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU`. Establish `hfin : FiniteDimensional ℂ U` using `(hV.aut φ hφ).zfin`. Establish `hle : U ≤ V` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)`. Establish `hst : ∀ x ∈ U, z x ∈ U` using `fun x hx => by`. Establish `: U ≤ U.comap z` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)`.

Conclude with `this hx`. Establish `hφU : φ ∈ U` using `Submodule.subset_span ⟨1, one_mem _, rfl⟩`. Establish `: Nontrivial U` using `⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩`. Take `⟨c, hc'⟩` from `Module.End.exists_eigenvalue (z.restrict hst)`. Take `⟨v, hv⟩` from `hc'.exists_hasEigenvector`.

Establish `hv1 : z v.1 = c • v.1` using `congrArg Subtype.val hv.apply_eq_smul`. Use `⟨c, fun ψ hψ => ?_⟩` and prove the remaining obligations. Break down `hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by` into its components or cases. Establish `h1 : z x = c • x` using `Module.End.mem_eigenspace_iff.1 hx.2`. Use `Module.End.mem_eigenspace_iff.2 ?_` and prove the remaining obligations.

Rewrite using `[← map_smul, ← h1]`. Conclude with `LinearMap.congr_fun (hc o).eq x⟩) with h | h`. Establish `: v.1 ∈ V ⊓ z.eigenspace c` using `⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩`. Rewrite `this` using `[h]`. Conclude with `absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2`.

Rewrite `hψ` using `[← h]`. Conclude with `Module.End.mem_eigenspace_iff.1 hψ.2`.
-/
theorem exists_scalar {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {V : Submodule ℂ (Sm E a)}
    (hV : IsDiscrete V) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

/- English proof (translation)
Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 hV.ne_bot`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_eq_one ℂ h0`. Take `⟨m, hm, h⟩` from `exists_multiset_qdet (Eop (a := N) τ) (((N : ℂ) - 1) / 2) φ f hf`. Use `⟨m, hm, fun u ψ hψ => ?_⟩` and prove the remaining obligations. Take `⟨c, h1⟩` from `exists_scalar hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (fun o => cap_commute_act' τ u o)`.

Establish `h2 : f (cap τ u φ) = _` using `h u`. Rewrite `h2` using `[h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one]`. Rewrite using `[h1 ψ hψ, h2]`.
-/
theorem exists_hasInfCharGL {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (τ : E →+* ℂ) : ∃ μ, HasInfCharGL V τ μ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := N) τ) (((N : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := exists_scalar hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (fun o => cap_commute_act' τ u o)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

/- English proof (translation)
Introduce `E _ _ _ N τ`. Use `⟨fun x => ⟨(CG.mk x).infChar τ, ?_⟩, fun V hV => exists_hasInfCharGL hV τ⟩` and prove the remaining obligations. Conclude with `hasInfChar_infChar_of_commute E N (fun τ u o => cap_commute_act' τ u o) (CG.mk x) τ`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (τ : E →+* ℂ), (∀ x : CuspSub E N, ∃ μ, x.HasInfChar τ μ) ∧ ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∃ μ, HasInfCharGL V τ μ := by
  intro E _ _ _ N τ
  refine ⟨fun x => ⟨(CG.mk x).infChar τ, ?_⟩, fun V hV => exists_hasInfCharGL hV τ⟩
  exact hasInfChar_infChar_of_commute E N (fun τ u o => cap_commute_act' τ u o) (CG.mk x) τ

end GlobalTheory.ResW.IrrInfChar

end
