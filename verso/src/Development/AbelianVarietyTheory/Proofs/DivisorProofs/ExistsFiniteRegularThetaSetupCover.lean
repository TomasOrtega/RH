import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

def USetup.regSet (X₁ : USetup C) : Set X₁.M.Z := {z | X₁.S.R ≤ X₁.M.O z}

/- English proof (translation)
Take `⟨s, hs⟩` from `X₁.S.fg`. Establish `e : X₁.regSet = ⋂ a ∈ s, {z | a ∈ X₁.M.O z}`. Use extensionality with `z`. Simplify using `only [USetup.regSet, Set.mem_setOf_eq, Set.mem_iInter]`. Rewrite using `[← hs, Algebra.adjoin_le_iff]`.

Conclude with `⟨fun h a ha => h ha, fun h a ha => h a ha⟩`. Rewrite using `[e]`. Conclude with `isOpen_biInter_finset fun a _ => X₁.M.isOpen_setOf_mem_O a`.
-/
theorem USetup.isOpen_regSet (X₁ : USetup C) : IsOpen X₁.regSet := by
  obtain ⟨s, hs⟩ := X₁.S.fg
  have e : X₁.regSet = ⋂ a ∈ s, {z | a ∈ X₁.M.O z} := by
    ext z
    simp only [USetup.regSet, Set.mem_setOf_eq, Set.mem_iInter]
    rw [← hs, Algebra.adjoin_le_iff]
    exact ⟨fun h a ha => h ha, fun h a ha => h a ha⟩
  rw [e]
  exact isOpen_biInter_finset fun a _ => X₁.M.isOpen_setOf_mem_O a

def USetup.cov (X₁ : USetup C) : Set (Xo.XF c) := {x | ∃ w ∈ X₁.regSet, X₁.π w = C.i x}

/- English proof (translation)
Use `haveI := X₁.fin`. Establish `hcl : IsClosedMap X₁.π` using `X₁.π.isClosedMap`. Establish `hF : IsClosed (X₁.π '' (closure {w} \ X₁.regSet))` using `hcl _ (isClosed_closure.sdiff X₁.isOpen_regSet)`. Use `⟨C.i ⁻¹' (X₁.π '' (closure {w} \ X₁.regSet))ᶜ, hF.isOpen_compl.preimage C.i.continuous, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨w', ⟨hw', hn⟩, he⟩`.

Establish `e` using `GlobalTheory.eq_of_specializes_of_isIntegralHom X₁.π (specializes_iff_mem_closure.2 hw') (hw.trans he.symm)`. Conclude with `hn (by rw [← e]; exact hR)`. Introduce and unpack `x ⟨hx, hxW⟩`. Establish `hs : C.i ξ ⤳ C.i x` using `(specializes_iff_mem_closure.2 hx).map C.i.continuous`. Establish `hT : closure {C.i ξ} ⊆ X₁.π '' closure {w}` using `(hcl _ isClosed_closure).closure_subset_iff.2 (Set.singleton_subset_iff.2 ⟨w, subset_closure rfl, hw⟩)`.

Take `⟨w', hw', he⟩` from `hT (specializes_iff_mem_closure.1 hs)`. Use `⟨w', ?_, he⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `hxW ⟨w', ⟨hw', hn⟩, he⟩`.
-/
theorem USetup.exists_open_cov {X₁ : USetup C} {ξ : Xo.XF c} {w : X₁.M.Z} (hw : X₁.π w = C.i ξ)
    (hR : X₁.S.R ≤ X₁.M.O w) : ∃ W : Set (Xo.XF c), IsOpen W ∧ ξ ∈ W ∧ closure {ξ} ∩ W ⊆ X₁.cov := by
  haveI := X₁.fin
  have hcl : IsClosedMap X₁.π := X₁.π.isClosedMap
  have hF : IsClosed (X₁.π '' (closure {w} \ X₁.regSet)) := hcl _ (isClosed_closure.sdiff X₁.isOpen_regSet)
  refine ⟨C.i ⁻¹' (X₁.π '' (closure {w} \ X₁.regSet))ᶜ, hF.isOpen_compl.preimage C.i.continuous, ?_, ?_⟩
  · rintro ⟨w', ⟨hw', hn⟩, he⟩
    have e := GlobalTheory.eq_of_specializes_of_isIntegralHom X₁.π (specializes_iff_mem_closure.2 hw') (hw.trans he.symm)
    exact hn (by rw [← e]; exact hR)
  · rintro x ⟨hx, hxW⟩
    have hs : C.i ξ ⤳ C.i x := (specializes_iff_mem_closure.2 hx).map C.i.continuous
    have hT : closure {C.i ξ} ⊆ X₁.π '' closure {w} :=
      (hcl _ isClosed_closure).closure_subset_iff.2
        (Set.singleton_subset_iff.2 ⟨w, subset_closure rfl, hw⟩)
    obtain ⟨w', hw', he⟩ := hT (specializes_iff_mem_closure.1 hs)
    refine ⟨w', ?_, he⟩
    by_contra hn
    exact hxW ⟨w', ⟨hw', hn⟩, he⟩

/- English proof (translation)
Use `haveI := Formalism.L2.Pj.CompFin.isNoetherian_XF Xo c`. It suffices to establish `key : ∀ T : TopologicalSpace.Closeds (Xo.XF c), ∃ s : Set (USetup C), s.Finite ∧ ∀ x ∈ T, ∃ X' ∈ s, x ∈ X'.cov by`. Take `⟨s, hs, hT⟩` from `key ⊤`. Conclude with `⟨s, hs, fun x => hT x trivial⟩`. Introduce `T`.

Proceed by induction on `T using WellFoundedLT.induction with`. Consider the case `_ T ih`. Distinguish the cases in `hirr : IsIrreducible (T : Set (Xo.XF c))`. Establish `hg` using `hirr.isGenericPoint_genericPoint_closure`. Rewrite `hg` using `[T.isClosed.closure_eq]`.

Take `⟨X', w, hw, hR⟩` from `h hirr.genericPoint`. Take `⟨W, hW, hξ, hcov⟩` from `USetup.exists_open_cov hw hR`. Set `T₁ : TopologicalSpace.Closeds (Xo.XF c)` to `⟨(T : Set (Xo.XF c)) \ W, T.isClosed.sdiff hW⟩`. Establish `hlt : T₁ < T`. Use `lt_of_le_of_ne (fun x hx => hx.1) fun e => ?_` and prove the remaining obligations.

Establish `hmem : hirr.genericPoint ∈ (T₁ : Set (Xo.XF c))`. Rewrite using `[e]`. Conclude with `hg.mem`. Conclude with `hmem.2 hξ`. Take `⟨s, hs, hsT⟩` from `ih T₁ hlt`.

Use `⟨insert X' s, hs.insert X', fun x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hxW : x ∈ W`. Conclude with `⟨X', Set.mem_insert _ _, hcov ⟨by rw [hg.def]; exact hx, hxW⟩⟩`. Take `⟨X'', h1, h2⟩` from `hsT x ⟨hx, hxW⟩`. Conclude with `⟨X'', Set.mem_insert_of_mem _ h1, h2⟩`.

Take `⟨S, hSi, hTS⟩` from `TopologicalSpace.NoetherianSpace.exists_finset_irreducible T`. Establish `hle : ∀ k ∈ S, k < T`. Introduce `k hk`. Use `lt_of_le_of_ne ?_ fun e => hirr (e ▸ hSi ⟨k, hk⟩)` and prove the remaining obligations. Rewrite using `[hTS]`.

Conclude with `Finset.le_sup (f := id) hk`. Establish `hk : ∀ k : S, ∃ s : Set (USetup C), s.Finite ∧ ∀ x ∈ (k : TopologicalSpace.Closeds (Xo.XF c)), ∃ X' ∈ s, x ∈ X'.cov` using `fun k => ih k (hle k k.2)`. Use `choose f hf hfT using hk`. Use `⟨⋃ k, f k, Set.finite_iUnion hf, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[hTS]`.

Establish `hx' : x ∈ ((S.sup id : TopologicalSpace.Closeds (Xo.XF c)) : Set (Xo.XF c))` using `hx`. Rewrite `hx'` using `[TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]`. Simplify using `only [Set.mem_iUnion, Function.comp_apply, id] at hx'`. Take `⟨k, hkS, hxk⟩` from `hx'`. Take `⟨X'', h1, h2⟩` from `hfT ⟨k, hkS⟩ x hxk`.

Conclude with `⟨X'', Set.mem_iUnion.2 ⟨_, h1⟩, h2⟩`.
-/
theorem USetup.exists_finite_cover
    (h : ∀ x : Xo.XF c, ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w) :
    ∃ s : Set (USetup C), s.Finite ∧ ∀ x : Xo.XF c, ∃ X' ∈ s, x ∈ X'.cov := by
  haveI := Formalism.L2.Pj.CompFin.isNoetherian_XF Xo c
  suffices key : ∀ T : TopologicalSpace.Closeds (Xo.XF c),
      ∃ s : Set (USetup C), s.Finite ∧ ∀ x ∈ T, ∃ X' ∈ s, x ∈ X'.cov by
    obtain ⟨s, hs, hT⟩ := key ⊤
    exact ⟨s, hs, fun x => hT x trivial⟩
  intro T
  induction T using WellFoundedLT.induction with
  | _ T ih =>
  by_cases hirr : IsIrreducible (T : Set (Xo.XF c))
  · have hg := hirr.isGenericPoint_genericPoint_closure
    rw [T.isClosed.closure_eq] at hg
    obtain ⟨X', w, hw, hR⟩ := h hirr.genericPoint
    obtain ⟨W, hW, hξ, hcov⟩ := USetup.exists_open_cov hw hR
    let T₁ : TopologicalSpace.Closeds (Xo.XF c) := ⟨(T : Set (Xo.XF c)) \ W, T.isClosed.sdiff hW⟩
    have hlt : T₁ < T := by
      refine lt_of_le_of_ne (fun x hx => hx.1) fun e => ?_
      have hmem : hirr.genericPoint ∈ (T₁ : Set (Xo.XF c)) := by
        rw [e]; exact hg.mem
      exact hmem.2 hξ
    obtain ⟨s, hs, hsT⟩ := ih T₁ hlt
    refine ⟨insert X' s, hs.insert X', fun x hx => ?_⟩
    by_cases hxW : x ∈ W
    · exact ⟨X', Set.mem_insert _ _, hcov ⟨by rw [hg.def]; exact hx, hxW⟩⟩
    · obtain ⟨X'', h1, h2⟩ := hsT x ⟨hx, hxW⟩
      exact ⟨X'', Set.mem_insert_of_mem _ h1, h2⟩
  · obtain ⟨S, hSi, hTS⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible T
    have hle : ∀ k ∈ S, k < T := by
      intro k hk
      refine lt_of_le_of_ne ?_ fun e => hirr (e ▸ hSi ⟨k, hk⟩)
      rw [hTS]
      exact Finset.le_sup (f := id) hk
    have hk : ∀ k : S, ∃ s : Set (USetup C), s.Finite ∧ ∀ x ∈ (k : TopologicalSpace.Closeds (Xo.XF c)),
        ∃ X' ∈ s, x ∈ X'.cov := fun k => ih k (hle k k.2)
    choose f hf hfT using hk
    refine ⟨⋃ k, f k, Set.finite_iUnion hf, fun x hx => ?_⟩
    rw [hTS] at hx
    have hx' : x ∈ ((S.sup id : TopologicalSpace.Closeds (Xo.XF c)) : Set (Xo.XF c)) := hx
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hx'
    simp only [Set.mem_iUnion, Function.comp_apply, id] at hx'
    obtain ⟨k, hkS, hxk⟩ := hx'
    obtain ⟨X'', h1, h2⟩ := hfT ⟨k, hkS⟩ x hxk
    exact ⟨X'', Set.mem_iUnion.2 ⟨_, h1⟩, h2⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c C h`. Take `⟨s, hs, hcov⟩` from `USetup.exists_finite_cover h`. Use `haveI := hs.to_subtype`. Take `⟨m, ⟨e⟩⟩` from `Finite.exists_equiv_fin s`. Use `⟨m, fun k => (e.symm k).1, fun k => ⟨(e.symm k).1.regSet, (e.symm k).1.isOpen_regSet⟩, fun k => fun a ha => RatModel.mem_ringOn.2 fun z hz => hz ha, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨X'', hX, w, hw, he⟩` from `hcov x`. Establish `key : ∀ Y : USetup C, Y = X'' → ∃ w ∈ Y.regSet, Y.π w = C.i x`. Introduce and unpack `Y rfl`. Conclude with `⟨w, hw, he⟩`. Conclude with `⟨e ⟨X'', hX⟩, key _ (by simp)⟩`.
-/
theorem exists_fin_uSetup_regular_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), (∀ x : Xo.XF c, ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w) → ∃ (m : ℕ) (X' : Fin m → USetup C) (U : ∀ k, (X' k).M.Z.Opens), (∀ k, (X' k).S.R ≤ (X' k).M.ringOn (U k)) ∧ ∀ x : Xo.XF c, ∃ k, ∃ w ∈ U k, (X' k).π w = C.i x := by
  intro E _ _ _ H Dw l Xo c C h
  obtain ⟨s, hs, hcov⟩ := USetup.exists_finite_cover h
  haveI := hs.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  refine ⟨m, fun k => (e.symm k).1, fun k => ⟨(e.symm k).1.regSet, (e.symm k).1.isOpen_regSet⟩,
    fun k => fun a ha => RatModel.mem_ringOn.2 fun z hz => hz ha, fun x => ?_⟩
  obtain ⟨X'', hX, w, hw, he⟩ := hcov x
  have key : ∀ Y : USetup C, Y = X'' → ∃ w ∈ Y.regSet, Y.π w = C.i x := by
    rintro Y rfl
    exact ⟨w, hw, he⟩
  exact ⟨e ⟨X'', hX⟩, key _ (by simp)⟩

end GlobalTheory.UPoinc
