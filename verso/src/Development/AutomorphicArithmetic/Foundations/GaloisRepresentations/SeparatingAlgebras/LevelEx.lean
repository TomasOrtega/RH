import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsOpenIsCompactSubgroupFiniteAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowValAdd
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `E _ _ _ a W f`. Take `⟨K0, hK0o, hK0c⟩` from `UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E a`. Set `C : Subgroup (UA E a)` to `K0.map (finU E a).subtype`. Establish `hCf : C ≤ finU E a`. Introduce and unpack `_ ⟨x, _, rfl⟩`.

Conclude with `x.2`. Establish `hCc : IsCompact (C : Set (UA E a))`. Establish `h` using `hK0c.image (continuous_subtype_val (p := fun x => x ∈ finU E a))`. Conclude with `h`. Establish `hCo : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E a ⊆ C`.

Take `⟨t, ht, hte⟩` from `isOpen_induced_iff.1 hK0o`. Use `⟨t, ht, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : finU E a) ∈ (K0 : Set (finU E a))` using `K0.one_mem`. Rewrite `h1` using `[← hte]`. Conclude with `h1`.

Introduce and unpack `x ⟨hxt, hxf⟩`. Establish `hx : (⟨x, hxf⟩ : finU E a) ∈ (K0 : Set (finU E a))`. Rewrite using `[← hte]`. Conclude with `hxt`. Conclude with `⟨⟨x, hxf⟩, hx, rfl⟩`.

Take `⟨hc, N, hN, h1, hNC⟩` from `GlobalTheory.CongSc.stab_level W f C hCf hCc hCo`. Conclude with `⟨C ⊓ GlobalTheory.CongSc.stab W f, ⟨inf_le_left.trans hCf, hc, N, hN, h1, hNC⟩, fun k hk v g => hk.2 v g⟩`.
-/
theorem UpperTheory.Gal.Gen.levelEx_pf :
    UpperTheory.Gal.Gen.LevelEx := by
  intro E _ _ _ a W f
  obtain ⟨K0, hK0o, hK0c⟩ := UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E a
  let C : Subgroup (UA E a) := K0.map (finU E a).subtype
  have hCf : C ≤ finU E a := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hCc : IsCompact (C : Set (UA E a)) := by
    have h := hK0c.image (continuous_subtype_val (p := fun x => x ∈ finU E a))
    exact h
  have hCo : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E a ⊆ C := by
    obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 hK0o
    refine ⟨t, ht, ?_, ?_⟩
    · have h1 : (1 : finU E a) ∈ (K0 : Set (finU E a)) := K0.one_mem
      rw [← hte] at h1
      exact h1
    · rintro x ⟨hxt, hxf⟩
      have hx : (⟨x, hxf⟩ : finU E a) ∈ (K0 : Set (finU E a)) := by
        rw [← hte]
        exact hxt
      exact ⟨⟨x, hxf⟩, hx, rfl⟩
  obtain ⟨hc, N, hN, h1, hNC⟩ := GlobalTheory.CongSc.stab_level W f C hCf hCc hCo
  exact ⟨C ⊓ GlobalTheory.CongSc.stab W f, ⟨inf_le_left.trans hCf, hc, N, hN, h1, hNC⟩, fun k hk v g => hk.2 v g⟩
