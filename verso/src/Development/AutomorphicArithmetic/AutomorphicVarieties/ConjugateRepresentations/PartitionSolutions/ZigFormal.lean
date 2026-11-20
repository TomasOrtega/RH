import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
open UpperTheory.V.Cj.A

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Proceed by induction. Treat this case separately. Treat this case separately.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Cj.A.zigFormal :
    ZigFormal := by
  intro Γ V S I _ _ _ _ d G
  refine ⟨fun q k u u' c h hz => ?_, fun ι hι q => ?_⟩
  · cases q with
    | zero => exact fun x hx => (h x hx).symm.trans (hz x hx)
    | succ q =>
      obtain ⟨b, hb, hdb, hz⟩ := hz
      exact ⟨b, hb, fun x hx => (hdb x hx).trans (h x hx), hz⟩
  · induction q with
    | zero => exact fun k u c hz x hx => hz (x.map ι) (by rw [List.length_map, hx])
    | succ q ih =>
      rintro k u c ⟨b, hb, hdb, hz⟩
      refine ⟨fun x => b (x.map ι), fun γ x hx => ?_, fun x hx => hdb (x.map ι) (by rw [List.length_map, hx]), ?_⟩
      · have h := hb γ (x.map ι) (by rw [List.length_map, hx])
        refine Eq.trans ?_ h
        simp only [List.map_map]
        congr 2
        funext δ
        exact hι γ δ
      · have h := ih (k + 1) _ c hz
        have e : (fun x : List Γ => UpperTheory.V.Lit.Geo.hd b (x.map ι)) = UpperTheory.V.Lit.Geo.hd (fun x : List Γ => b (x.map ι)) :=
          funext fun x => (hdFacts.2.2.1 I Γ _ ι b x).symm
        rw [e] at h
        exact h
