import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerWhitCharReflect

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.PRep.WhitQuot

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `key : ∀ (g : G) (v : A.toSubmodule), (subQuot A B) g ((B.toSubmodule.comap A.toSubmodule.subtype).mkQ v) = (B.toSubmodule.comap A.toSubmodule.subtype).mkQ (A.toRepresentation g v)` using `fun _ _ => rfl`. Unfold `twKer`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, w, rfl⟩`.

Take `⟨v, rfl⟩` from `(B.toSubmodule.comap A.toSubmodule.subtype).mkQ_surjective w`. Establish `h : (subQuot A B) n ((B.toSubmodule.comap A.toSubmodule.subtype).mkQ v) - ((χ n : ℂˣ) : ℂ) • (B.toSubmodule.comap A.toSubmodule.subtype).mkQ v = (B.toSubmodule.comap A.toSubmodule.subtype).mkQ (A.toRepresentation n v - ((χ n : ℂˣ) : ℂ) • v)`. Rewrite using `[key, map_sub, map_smul]`. Rewrite using `[h]`. Conclude with `Submodule.mem_map_of_mem (Submodule.subset_span ⟨n, v, rfl⟩)`.

Rewrite using `[Submodule.map_le_iff_le_comap]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, v, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, ← key]`. Conclude with `Submodule.subset_span ⟨n, _, rfl⟩`.
-/
theorem twKer_subQuot {ρ : Representation ℂ G V} (A B : Subrepresentation ρ) (U : Subgroup G) (χ : U →* ℂˣ) :
    twKer (subQuot A B) U χ =
      (twKer A.toRepresentation U χ).map (B.toSubmodule.comap A.toSubmodule.subtype).mkQ := by
  have key : ∀ (g : G) (v : A.toSubmodule),
      (subQuot A B) g ((B.toSubmodule.comap A.toSubmodule.subtype).mkQ v) =
        (B.toSubmodule.comap A.toSubmodule.subtype).mkQ (A.toRepresentation g v) := fun _ _ => rfl
  unfold twKer
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨n, w, rfl⟩
    obtain ⟨v, rfl⟩ := (B.toSubmodule.comap A.toSubmodule.subtype).mkQ_surjective w
    have h : (subQuot A B) n ((B.toSubmodule.comap A.toSubmodule.subtype).mkQ v) -
          ((χ n : ℂˣ) : ℂ) • (B.toSubmodule.comap A.toSubmodule.subtype).mkQ v =
        (B.toSubmodule.comap A.toSubmodule.subtype).mkQ
          (A.toRepresentation n v - ((χ n : ℂˣ) : ℂ) • v) := by
      rw [key, map_sub, map_smul]
    rw [h]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨n, v, rfl⟩)
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, ← key]
    exact Submodule.subset_span ⟨n, _, rfl⟩

/- English proof (translation)
Establish `h : twKer A.toRepresentation U χ ≤ (twKer ρ U χ).comap A.toSubmodule.subtype`. Unfold `twKer`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, v, rfl⟩`. Conclude with `Submodule.subset_span ⟨n, v, rfl⟩`.

Conclude with `h hx`.
-/
theorem coe_mem_twKer {ρ : Representation ℂ G V} (A : Subrepresentation ρ) (U : Subgroup G) (χ : U →* ℂˣ)
    {x : A.toSubmodule} (hx : x ∈ twKer A.toRepresentation U χ) : (x : V) ∈ twKer ρ U χ := by
  have h : twKer A.toRepresentation U χ ≤ (twKer ρ U χ).comap A.toSubmodule.subtype := by
    unfold twKer
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    exact Submodule.subset_span ⟨n, v, rfl⟩
  exact h hx

end General

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ N V _ _ ρ hρ A B hBA`. Establish `hsm : IsSmooth A.toRepresentation`. Introduce `v`. Establish `h : {g : GL (Fin N) k | A.toRepresentation g v = v} = {g | ρ g (v : V) = v}` using `Set.ext fun g => Subtype.ext_iff`. Rewrite using `[h]`.

Conclude with `hρ v`. Use `show Nontrivial (_ ⧸ twKer (subQuot A B) (unipB k (Fin N)) (whitChar ψ N)) ↔ _`. Rewrite using `[Submodule.Quotient.nontrivial_iff, twKer_subQuot, Ne, Submodule.map_mkQ_eq_top]`. Use `not_congr ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Introduce `v hv`.

Establish `hmem : (⟨v, hv⟩ : A.toSubmodule) ∈ B.toSubmodule.comap A.toSubmodule.subtype ⊔ twKer A.toRepresentation (unipB k (Fin N)) (whitChar ψ N)`. Rewrite using `[h]`. Conclude with `Submodule.mem_top`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 hmem`. Establish `hv' : v = (y : V) + (z : V)` using `by rw [← Submodule.coe_add, hyz]`.

Rewrite using `[hv']`. Conclude with `Submodule.add_mem_sup hy (coe_mem_twKer A _ _ hz)`. Rewrite using `[eq_top_iff]`. Introduce and unpack `a -`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 (h a.2)`.

Establish `hyA : y ∈ A.toSubmodule` using `hBA hy`. Establish `hzA : z ∈ A.toSubmodule`. Establish `hz2 : z = (a : V) - y` using `by rw [← hyz]; abel`. Rewrite using `[hz2]`. Conclude with `A.toSubmodule.sub_mem a.2 hyA`.

Establish `hz' : (⟨z, hzA⟩ : A.toSubmodule) ∈ twKer A.toRepresentation (unipB k (Fin N)) (whitChar ψ N)` using `GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N A.toRepresentation ρ hsm hρ A.toSubmodule.subtype A.toSubmodule.injective_subtype (fun _ _ => rfl) _ hz`. Establish `ha : a = ⟨y, hyA⟩ + ⟨z, hzA⟩` using `Subtype.ext hyz.symm`. Rewrite using `[ha]`. Conclude with `Submodule.add_mem_sup hy hz'`.
-/
theorem isGenericFor_subQuot_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ A B : Subrepresentation ρ, B ≤ A → (IsGenericFor ψ (subQuot A B) ↔ ¬ A.toSubmodule ≤ B.toSubmodule ⊔ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ A B hBA
  have hsm : IsSmooth A.toRepresentation := by
    intro v
    have h : {g : GL (Fin N) k | A.toRepresentation g v = v} = {g | ρ g (v : V) = v} :=
      Set.ext fun g => Subtype.ext_iff
    rw [h]
    exact hρ v
  show Nontrivial (_ ⧸ twKer (subQuot A B) (unipB k (Fin N)) (whitChar ψ N)) ↔ _
  rw [Submodule.Quotient.nontrivial_iff, twKer_subQuot, Ne, Submodule.map_mkQ_eq_top]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · intro v hv
    have hmem : (⟨v, hv⟩ : A.toSubmodule) ∈ B.toSubmodule.comap A.toSubmodule.subtype ⊔
        twKer A.toRepresentation (unipB k (Fin N)) (whitChar ψ N) := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    have hv' : v = (y : V) + (z : V) := by rw [← Submodule.coe_add, hyz]
    rw [hv']
    exact Submodule.add_mem_sup hy (coe_mem_twKer A _ _ hz)
  · rw [eq_top_iff]
    rintro a -
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h a.2)
    have hyA : y ∈ A.toSubmodule := hBA hy
    have hzA : z ∈ A.toSubmodule := by
      have hz2 : z = (a : V) - y := by rw [← hyz]; abel
      rw [hz2]
      exact A.toSubmodule.sub_mem a.2 hyA
    have hz' : (⟨z, hzA⟩ : A.toSubmodule) ∈ twKer A.toRepresentation (unipB k (Fin N)) (whitChar ψ N) :=
      GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N A.toRepresentation ρ hsm hρ
        A.toSubmodule.subtype A.toSubmodule.injective_subtype (fun _ _ => rfl) _ hz
    have ha : a = ⟨y, hyA⟩ + ⟨z, hzA⟩ := Subtype.ext hyz.symm
    rw [ha]
    exact Submodule.add_mem_sup hy hz'

end GlobalTheory.CompanionTheory.PRep.WhitQuot
