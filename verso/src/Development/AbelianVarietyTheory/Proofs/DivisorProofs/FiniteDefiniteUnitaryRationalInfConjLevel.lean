import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEmbeddingEntryDefiniteUnitaryRationalPointLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNumberFieldBddDenomConjNormLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorDefiniteUnitaryConjugateStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.StabFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
The claim follows from `congrArg (fun g : GL (Fin n) (Af E) => pLoc E w (g.val i j)) (GlobalTheory.BCT.FinPart.pU_finPt γ)`.
-/
theorem cLoc_finPt (γ : UE E n) (w : Pl E) (i j : Fin n) :
    (cLoc w ((finPt γ : finU E n) : UA E n)).val i j = algebraMap E (w.adicCompletion E) ((γ : GL (Fin n) E).val i j) :=
  congrArg (fun g : GL (Fin n) (Af E) => pLoc E w (g.val i j)) (GlobalTheory.BCT.FinPart.pU_finPt γ)

/- English proof (translation)
Introduce `w hw`. Take `⟨k, hk, e⟩` from `Subgroup.mem_map.1 hg`. Establish `e' : x⁻¹ * g * x = k`. Rewrite using `[← e]`. Simplify using `[MulAut.conj_apply, mul_assoc]`.

Rewrite using `[e']`. Establish `hk' : ∀ u ∈ S, ∃ a ∈ K' u, (a : GLw n u) = cLoc u k.1`. Simplify `hk` using `[globLev, Subgroup.mem_iInf]`. Take `⟨a, ha, hae⟩` from `hk' w hw`. Rewrite using `[← hae]`.

Conclude with `Subgroup.mem_subgroupOf.1 ((hK.1 w).2.1 ha)`.
-/
theorem cLoc_conj_mem_KGL {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K') (x g : finU E n)
    (hg : g ∈ (globLev S K').map (MulAut.conj x).toMonoidHom) :
    ∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU E n) : UA E n) ∈ GlobalTheory.LFun.KGL w n := by
  intro w hw
  obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 hg
  have e' : x⁻¹ * g * x = k := by
    rw [← e]
    simp [MulAut.conj_apply, mul_assoc]
  rw [e']
  have hk' : ∀ u ∈ S, ∃ a ∈ K' u, (a : GLw n u) = cLoc u k.1 := by
    simpa [globLev, Subgroup.mem_iInf] using hk
  obtain ⟨a, ha, hae⟩ := hk' w hw
  rw [← hae]
  exact Subgroup.mem_subgroupOf.1 ((hK.1 w).2.1 ha)

end GlobalTheory.BCT.StabFin

open GlobalTheory.BCT.StabFin in

/- English proof (translation)
Introduce `E _ _ _ _ n _ S hS K' hK x`. Take `⟨d, hd, hC⟩` from `GlobalTheory.T.exists_bounded_denominator_definiteUnitary_conjugate E n S hS x`. Use `haveI : Finite {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} := (GlobalTheory.T.finite_numberField_bdd_denom_conj_norm_le_one E d hd).to_subtype`. Establish `hrat` using `(GlobalTheory.BCT.FinPart.finPt_props E n).2.2`. Set `γ : ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) → UE E n` to `fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose`.

Establish `hγ : ∀ g, finPt (γ g) = g.1` using `fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose_spec`. Use `Finite.of_injective (β := Fin n → Fin n → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1}) (fun g i j => ⟨((γ g : UE E n) : GL (Fin n) E).val i j, fun w => by` and prove the remaining obligations. Use `hC g.1 (cLoc_conj_mem_KGL hK x g.1 (Subgroup.mem_inf.1 g.2).2) w i j` as an intermediate fact. Rewrite using `[← hγ g, cLoc_finPt] at this,` and apply the resulting hypothesis. Use `fun τ => GlobalTheory.T.norm_embedding_entry_definiteUnitaryRationalPoint_le_one E n (γ g) τ i j⟩) fun g g' e => ?_`.

Establish `e1 : γ g = γ g'`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `congrArg Subtype.val (congrFun (congrFun e i) j)`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hγ g, ← hγ g', e1]`.
-/
theorem GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU E n, Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) := by
  intro E _ _ _ _ n _ S hS K' hK x
  obtain ⟨d, hd, hC⟩ := GlobalTheory.T.exists_bounded_denominator_definiteUnitary_conjugate E n S hS x
  haveI : Finite {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈
      w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} := (GlobalTheory.T.finite_numberField_bdd_denom_conj_norm_le_one E d hd).to_subtype
  have hrat := (GlobalTheory.BCT.FinPart.finPt_props E n).2.2
  let γ : ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) → UE E n :=
    fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose
  have hγ : ∀ g, finPt (γ g) = g.1 := fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose_spec
  refine Finite.of_injective (β := Fin n → Fin n → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) *
      algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1})
    (fun g i j => ⟨((γ g : UE E n) : GL (Fin n) E).val i j, fun w => by
        have := hC g.1 (cLoc_conj_mem_KGL hK x g.1 (Subgroup.mem_inf.1 g.2).2) w i j
        rwa [← hγ g, cLoc_finPt] at this,
      fun τ => GlobalTheory.T.norm_embedding_entry_definiteUnitaryRationalPoint_le_one E n (γ g) τ i j⟩) fun g g' e => ?_
  have e1 : γ g = γ g' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact congrArg Subtype.val (congrFun (congrFun e i) j)
  apply Subtype.ext
  rw [← hγ g, ← hγ g', e1]
