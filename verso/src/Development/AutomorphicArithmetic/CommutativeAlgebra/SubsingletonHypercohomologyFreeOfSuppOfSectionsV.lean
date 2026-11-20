import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppoStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSubsingletonCoh
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

/- English proof (translation)
Introduce `Q G hG P hP n`. Apply `UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology` to reduce the goal to its premises. Use `haveI : (res ℤ G).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ G).1`. Use `GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support ℤ (disc.obj P) (res ℤ G) ?_ n` and prove the remaining obligations. Introduce `U hU m b hb`.

Establish `hQ : Q U` using `hP U hU`. Use `haveI : Subsingleton (Sec G U) := hG U hQ`. Take `⟨h0, -, h3, hneg⟩` from `GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ G U`. Establish `hz : ∀ (c : Sec ((res ℤ G).X m) U), b = c → c = 0 → Loc U fun V g => ∃ a : Sec ((res ℤ G).X (m - 1)) V, Sec.map ((res ℤ G).d (m - 1) m) a = Sec.res g b`. Introduce and unpack `c rfl rfl`.

Use `⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Break down `lt_trichotomy m 0 with h | h | h` into its components or cases. Use `haveI := hneg m h`. Conclude with `hz b rfl (Subsingleton.elim _ _)`.

Substitute `h` using the available equality. Take `⟨a, rfl⟩` from `(h0 b).1 hb`. Use `hz _ rfl ?_` and prove the remaining obligations. Rewrite using `[Subsingleton.elim a 0]`. Simplify using the standard rewrite rules.

Conclude with `h3 (m - 1) m (m + 1) h (by omega) b rfl hb`.
-/
theorem UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish :
    ∀ (Q : Scheme.{0} → Prop) (G : Shv ℤ), (∀ U : Scheme.{0}, Q U → Subsingleton (Sec G U)) → ∀ P : PSh, Supp Q P → ∀ n : ℤ, Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) G n) := by
  intro Q G hG P hP n
  apply UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology
  haveI : (res ℤ G).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ G).1
  refine GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support ℤ (disc.obj P) (res ℤ G) ?_ n
  intro U hU m b hb
  have hQ : Q U := hP U hU
  haveI : Subsingleton (Sec G U) := hG U hQ
  obtain ⟨h0, -, h3, hneg⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ G U
  have hz : ∀ (c : Sec ((res ℤ G).X m) U), b = c → c = 0 →
      Loc U fun V g => ∃ a : Sec ((res ℤ G).X (m - 1)) V,
        Sec.map ((res ℤ G).d (m - 1) m) a = Sec.res g b := by
    rintro c rfl rfl
    refine ⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => ⟨0, ?_⟩⟩
    simp
  rcases lt_trichotomy m 0 with h | h | h
  · haveI := hneg m h
    exact hz b rfl (Subsingleton.elim _ _)
  · subst h
    obtain ⟨a, rfl⟩ := (h0 b).1 hb
    refine hz _ rfl ?_
    rw [Subsingleton.elim a 0]
    simp
  · exact h3 (m - 1) m (m + 1) h (by omega) b rfl hb
