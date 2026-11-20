import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

/- English proof (translation)
Introduce `E _ _ _ n`. Use `haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)`. Take `⟨U0, hU0o, hU0c⟩` from `GlobalTheory.GLIntegral.exists_isOpen_isCompact E n`. Set `p : finU E n →* GL (Fin n) (Af E)` to `(GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU E n).subtype)`. Establish `hp : Continuous p` using `continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)`.

Establish `hKo : IsOpen (U0.comap p : Set (finU E n))` using `hU0o.preimage hp`. Establish `hfin : ∀ x : UA E n, x ∈ finU E n ↔ finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1` using `hx`. Conclude with `ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])`. Introduce `hx`. Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map (pInf E) (x : GA E n) = 1`. Rewrite using `[← hx, pInf_finGL]`.

Establish `hc : IsClosed ((finU E n : Subgroup (UA E n)) : Set (UA E n))`. Establish `e : ((finU E n : Subgroup (UA E n)) : Set (UA E n)) = {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)}` using `Set.ext hfin`. Rewrite using `[e]`. Conclude with `isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val)) continuous_subtype_val`. Establish `hι : Topology.IsClosedEmbedding (fun x : finU E n => ((x : UA E n) : GA E n))` using `GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal`.

Conclude with `⟨U0.comap p, hKo, IsCompact.of_isClosed_subset (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL)) (Subgroup.isClosed_of_isOpen _ hKo) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩⟩`.
-/
theorem UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ K : Subgroup (finU E n), IsOpen (K : Set (finU E n)) ∧ IsCompact (K : Set (finU E n)) := by
  intro E _ _ _ n
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : finU E n →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU E n).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hKo : IsOpen (U0.comap p : Set (finU E n)) := hU0o.preimage hp
  have hfin : ∀ x : UA E n, x ∈ finU E n ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU E n : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU E n : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU E n => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  exact ⟨U0.comap p, hKo, IsCompact.of_isClosed_subset
    (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL))
    (Subgroup.isClosed_of_isOpen _ hKo) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩⟩
