import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

namespace GlobalTheory.ThKLocSS

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Introduce `t ht x hx`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hA t ht a ha) (hB t ht b hb)`.
-/
theorem opStable_sup' {T : Set (Module.End ℂ V)} {A B : Submodule ℂ V} (hA : OpStable T A) (hB : OpStable T B) :
    OpStable T (A ⊔ B) := by
  intro t ht x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem_sup (hA t ht a ha) (hB t ht b hb)

/- English proof (translation)
Introduce `t ht x hx` and use `⟨hA t ht x hx.1, hB t ht x hx.2⟩`.
-/
theorem opStable_inf' {T : Set (Module.End ℂ V)} {A B : Submodule ℂ V} (hA : OpStable T A) (hB : OpStable T B) :
    OpStable T (A ⊓ B) := fun t ht x hx => ⟨hA t ht x hx.1, hB t ht x hx.2⟩

/- English proof (translation)
Set `s : Set (Submodule ℂ V)` to `{C | N ≤ C ∧ C ≤ D ∧ OpStable T C ∧ P ⊓ C = N}`. Establish `hNs : N ∈ s` using `⟨le_rfl, hND, hN, inf_eq_right.2 hNP⟩`. Take `⟨C, -, hCmax⟩` from `zorn_le_nonempty₀ s (fun c hcs hc y hy => by`. Establish `hdir : DirectedOn (· ≤ ·) c` using `hc.directedOn`. Establish `hne : c.Nonempty` using `⟨y, hy⟩`.

Use `⟨sSup c, ⟨le_trans (hcs hy).1 (le_sSup hy), sSup_le fun z hz => (hcs hz).2.1, ?_, ?_⟩, fun z hz => le_sSup hz⟩` and prove the remaining obligations. Introduce `t ht x hx`. Take `⟨z, hz, hxz⟩` from `(Submodule.mem_sSup_of_directed hne hdir).1 hx`. Conclude with `le_sSup hz ((hcs hz).2.2.1 t ht x hxz)`. Use `le_antisymm ?_ (le_inf hNP (le_trans (hcs hy).1 (le_sSup hy)))` and prove the remaining obligations.

Introduce `x hx`. Take `⟨z, hz, hxz⟩` from `(Submodule.mem_sSup_of_directed hne hdir).1 hx.2`. Rewrite using `[← (hcs hz).2.2.2]`. Conclude with `⟨hx.1, hxz⟩) N hNs`. Take `⟨hNC, hCD, hC, hPC⟩` from `hCmax.prop`.

Use `⟨C, hCD, hC, ?_, hPC⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hPCD : P ⊔ C ≤ D` using `sup_le hPD hCD`. Establish `hex : ∃ S, S ≤ D ∧ IsSimpleOver T N S ∧ ¬ S ≤ P ⊔ C`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Apply `hne` to reduce the goal to its premises. Use `le_antisymm hPCD ?_` and prove the remaining obligations. Rewrite using `[← hsoc]`. Conclude with `sup_le (le_trans hNP le_sup_left) (sSup_le fun S hS => hall S hS.1 hS.2)`.

Take `⟨S, hSD, hS, hSnot⟩` from `hex`. Establish `hNS : N ≤ S` using `hS.1.le`. Establish `hPCst : OpStable T (P ⊔ C)` using `opStable_sup' hP hC`. Establish `hmeet : S ⊓ (P ⊔ C) = N`. Break down `hS.2.2 (S ⊓ (P ⊔ C)) (le_inf hNS (le_trans hNP le_sup_left)) inf_le_left (opStable_inf' hS.2.1 hPCst) with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd (h ▸ inf_le_right) hSnot`. Establish `hC's : C ⊔ S ∈ s`. Use `⟨le_trans hNC le_sup_left, sup_le hCD hSD, opStable_sup' hC hS.2.1, ?_⟩` and prove the remaining obligations. Use `le_antisymm ?_ (le_inf hNP (le_trans hNC le_sup_left))` and prove the remaining obligations.

Establish `h1 : (C ⊔ S) ⊓ (P ⊔ C) = C`. Rewrite using `[sup_inf_assoc_of_le S (le_sup_right : C ≤ P ⊔ C), hmeet, sup_eq_left.2 hNC]`. Combine the equalities or inequalities in the displayed calculation. Establish `hle : C ⊔ S ≤ C` using `hCmax.2 hC's le_sup_left`. Conclude with `hSnot (le_trans (le_trans le_sup_right hle) le_sup_right)`.
-/
theorem exists_opStable_compl_of_socleOver_eq (V : Type) [AddCommGroup V] [Module ℂ V] (T : Set (Module.End ℂ V))
    (N D P : Submodule ℂ V) (hND : N ≤ D) (hN : OpStable T N) (hsoc : socleOver T N D = D) (hNP : N ≤ P)
    (hPD : P ≤ D) (hP : OpStable T P) :
    ∃ C : Submodule ℂ V, C ≤ D ∧ OpStable T C ∧ P ⊔ C = D ∧ P ⊓ C = N := by
  classical
  let s : Set (Submodule ℂ V) := {C | N ≤ C ∧ C ≤ D ∧ OpStable T C ∧ P ⊓ C = N}
  have hNs : N ∈ s := ⟨le_rfl, hND, hN, inf_eq_right.2 hNP⟩
  obtain ⟨C, -, hCmax⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    have hne : c.Nonempty := ⟨y, hy⟩
    refine ⟨sSup c, ⟨le_trans (hcs hy).1 (le_sSup hy), sSup_le fun z hz => (hcs hz).2.1, ?_, ?_⟩,
      fun z hz => le_sSup hz⟩
    · intro t ht x hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact le_sSup hz ((hcs hz).2.2.1 t ht x hxz)
    · refine le_antisymm ?_ (le_inf hNP (le_trans (hcs hy).1 (le_sSup hy)))
      intro x hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx.2
      rw [← (hcs hz).2.2.2]
      exact ⟨hx.1, hxz⟩) N hNs
  obtain ⟨hNC, hCD, hC, hPC⟩ := hCmax.prop
  refine ⟨C, hCD, hC, ?_, hPC⟩
  by_contra hne
  have hPCD : P ⊔ C ≤ D := sup_le hPD hCD
  have hex : ∃ S, S ≤ D ∧ IsSimpleOver T N S ∧ ¬ S ≤ P ⊔ C := by
    by_contra hall
    push_neg at hall
    apply hne
    refine le_antisymm hPCD ?_
    rw [← hsoc]
    exact sup_le (le_trans hNP le_sup_left) (sSup_le fun S hS => hall S hS.1 hS.2)
  obtain ⟨S, hSD, hS, hSnot⟩ := hex
  have hNS : N ≤ S := hS.1.le
  have hPCst : OpStable T (P ⊔ C) := opStable_sup' hP hC
  have hmeet : S ⊓ (P ⊔ C) = N := by
    rcases hS.2.2 (S ⊓ (P ⊔ C)) (le_inf hNS (le_trans hNP le_sup_left)) inf_le_left
      (opStable_inf' hS.2.1 hPCst) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hSnot
  have hC's : C ⊔ S ∈ s := by
    refine ⟨le_trans hNC le_sup_left, sup_le hCD hSD, opStable_sup' hC hS.2.1, ?_⟩
    refine le_antisymm ?_ (le_inf hNP (le_trans hNC le_sup_left))
    have h1 : (C ⊔ S) ⊓ (P ⊔ C) = C := by
      rw [sup_inf_assoc_of_le S (le_sup_right : C ≤ P ⊔ C), hmeet, sup_eq_left.2 hNC]
    calc P ⊓ (C ⊔ S) ≤ P ⊓ ((C ⊔ S) ⊓ (P ⊔ C)) :=
          le_inf inf_le_left (le_inf inf_le_right (le_trans inf_le_left le_sup_left))
      _ = P ⊓ C := by rw [h1]
      _ = N := hPC
  have hle : C ⊔ S ≤ C := hCmax.2 hC's le_sup_left
  exact hSnot (le_trans (le_trans le_sup_right hle) le_sup_right)

end GlobalTheory.ThKLocSS
