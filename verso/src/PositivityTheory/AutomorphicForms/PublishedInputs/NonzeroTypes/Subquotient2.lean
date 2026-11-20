import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.Subquotient₂

variable {F H V : Type} [Field F] [Group H] [AddCommGroup V] [Module F V]

/- English proof (translation)
Establish `hN` using `(isFiniteLength_iff_isNoetherian_isArtinian.mp h).1`. Use `isNoetherian_iff'.mp hN` as an intermediate fact. Conclude with `(Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).strictMono.wellFoundedGT`.
-/
theorem wellFoundedGT_of_finiteLength {ρ : Representation F H V} (h : HasFiniteLength ρ) :
    WellFoundedGT (Subrepresentation ρ) := by
  have hN := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).1
  have := isNoetherian_iff'.mp hN
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).strictMono.wellFoundedGT

/- English proof (translation)
Establish `hA` using `(isFiniteLength_iff_isNoetherian_isArtinian.mp h).2`. Establish `: WellFoundedLT (Submodule (MonoidAlgebra F H) ρ.asModule)` using `hA`. Conclude with `(Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).strictMono.wellFoundedLT`.
-/
theorem wellFoundedLT_of_finiteLength {ρ : Representation F H V} (h : HasFiniteLength ρ) :
    WellFoundedLT (Subrepresentation ρ) := by
  have hA := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2
  have : WellFoundedLT (Submodule (MonoidAlgebra F H) ρ.asModule) := hA
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).strictMono.wellFoundedLT

/- English proof (translation)
Use `wellFoundedGT_of_finiteLength h` as an intermediate fact. Use `wellFoundedLT_of_finiteLength h` as an intermediate fact. Take `⟨T, hT, hmax⟩` from `wellFounded_gt.has_min {T : Subrepresentation ρ | y ∉ T.toSubmodule} ⟨⊥, fun h' => hy ((Submodule.mem_bot F).1 h')⟩`. Establish `hTtop : T ≠ ⊤`. Introduce and unpack `rfl`.

Conclude with `hT trivial`. Take `⟨S, hS, hmin⟩` from `wellFounded_lt.has_min {S : Subrepresentation ρ | T < S} ⟨⊤, lt_top_iff_ne_top.2 hTtop⟩`. Use `⟨S, T, ⟨hS, fun U hTU hUS => hmin U hTU hUS⟩, ?_, hT⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hyS`. Conclude with `hmax S hyS hS`.
-/
theorem exists_covBy {ρ : Representation F H V} (h : HasFiniteLength ρ) {y : V} (hy : y ≠ 0) :
    ∃ S T : Subrepresentation ρ, T ⋖ S ∧ y ∈ S.toSubmodule ∧ y ∉ T.toSubmodule := by
  have := wellFoundedGT_of_finiteLength h
  have := wellFoundedLT_of_finiteLength h
  obtain ⟨T, hT, hmax⟩ := wellFounded_gt.has_min {T : Subrepresentation ρ | y ∉ T.toSubmodule}
    ⟨⊥, fun h' => hy ((Submodule.mem_bot F).1 h')⟩
  have hTtop : T ≠ ⊤ := by
    rintro rfl
    exact hT trivial
  obtain ⟨S, hS, hmin⟩ := wellFounded_lt.has_min {S : Subrepresentation ρ | T < S}
    ⟨⊤, lt_top_iff_ne_top.2 hTtop⟩
  refine ⟨S, T, ⟨hS, fun U hTU hUS => hmin U hTU hUS⟩, ?_, hT⟩
  by_contra hyS
  exact hmax S hyS hS

end UpperTheory.TNZ.Grp.Subquotient₂

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `W _ _ ρ hs hfl hη`. Take `⟨y, hy, hyη⟩` from `hη`. Take `⟨S, T, hcov, hyS, hyT⟩` from `Subquotient₂.exists_covBy hfl hy`. Set `p : S.toRepresentation.IntertwiningMap (subQuot S T)` to `⟨Submodule.mkQ _, fun _ => rfl⟩`. Establish `hsq : IsSubquotient (subQuot S T) ρ` using `⟨S, p, Submodule.mkQ_surjective _⟩`.

Use `⟨_, inferInstance, inferInstance, subQuot S T, hsq.isSmooth hs, isIrreducible_subQuot hcov, hsq, Submodule.Quotient.mk ⟨y, hyS⟩, ?_, fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Submodule.Quotient.mk_eq_zero]`. Conclude with `hyT`. Use `show Submodule.Quotient.mk (S.toRepresentation m ⟨y, hyS⟩) = _`. Rewrite using `[← Submodule.Quotient.mk_smul]`.

Use `congr 1`. Conclude with `Subtype.ext (hyη m hm)`.
-/
theorem step_subq {n : ℕ} (G : Grp k n) : G.SubquotientProp := by
  intro W _ _ ρ hs hfl hη
  obtain ⟨y, hy, hyη⟩ := hη
  obtain ⟨S, T, hcov, hyS, hyT⟩ := Subquotient₂.exists_covBy hfl hy
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
  refine ⟨_, inferInstance, inferInstance, subQuot S T, hsq.isSmooth hs, isIrreducible_subQuot hcov, hsq,
    Submodule.Quotient.mk ⟨y, hyS⟩, ?_, fun m hm => ?_⟩
  · rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hyT
  · show Submodule.Quotient.mk (S.toRepresentation m ⟨y, hyS⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hyη m hm)

end UpperTheory.TNZ.Grp
