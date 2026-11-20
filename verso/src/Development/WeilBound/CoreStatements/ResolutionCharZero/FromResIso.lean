import Mathlib
import Development.ResolutionOfSingularities.Statements
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace PositivityTheory.ResPlug.FromRes

open FunctorialResolution

/- English proof (translation)
Establish `h : IsIso (f ∣_ (g ⁻¹ᵁ V) ≫ g ∣_ V)` using `@IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2`. Rewrite using `[morphismRestrict_comp]`. Conclude with `h`.
-/
private theorem isIso_restrict_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Opens)
    (h1 : IsIso (f ∣_ (g ⁻¹ᵁ V))) (h2 : IsIso (g ∣_ V)) : IsIso ((f ≫ g) ∣_ V) := by
  have h : IsIso (f ∣_ (g ⁻¹ᵁ V) ≫ g ∣_ V) := @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  rw [morphismRestrict_comp]
  exact h

/- English proof (translation)
Simplify using `only [BlowupSequence.structMap, BlowupSequence.down]`. Establish `: (homOfLE (Nat.zero_le 0)).op = 𝟙 (op (0 : ℕ))` using `Subsingleton.elim _ _`. Rewrite using `[this, CategoryTheory.Functor.map_id, Category.id_comp]`.
-/
private theorem structMap_zero' {X : Scheme.{0}} (s : BlowupSequence X) : s.structMap 0 = s.isoZero.hom := by
  simp only [BlowupSequence.structMap, BlowupSequence.down]
  have : (homOfLE (Nat.zero_le 0)).op = 𝟙 (op (0 : ℕ)) := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.id_comp]

/- English proof (translation)
Take `⟨ideal, boundary, h0, -, -, -, hle, hsucc, -, -, -, -, -⟩` from `h`. Establish `hsupp : ∀ i, i ≤ s.length → ∀ x ∈ ((ideal i).support : Set (s.obj i)), (s.structMap i).base x ∈ (I.support : Set X)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`.

Introduce `_ x hx`. Rewrite `hx` using `[h0, Scheme.IdealSheafData.support_comap]`. Conclude with `hx`. Consider the case `succ i ih`. Introduce `hi x hx`.

Establish `hlt : i < s.length` using `hi`. Establish `e` using `congrArg Scheme.IdealSheafData.support (hsucc i hlt)`. Rewrite `e` using `[Scheme.IdealSheafData.support_mul]`. Establish `hx' : x ∈ (((s.center i).comap (s.blowupMap i)).support ⊔ (ideal (i + 1)).support : Closeds _)` using `Or.inr hx`. Rewrite `hx'` using `[e, Scheme.IdealSheafData.support_comap]`.

Use `ih hlt.le _ hx'` as an intermediate fact. Rewrite using `[← s.structMap_down (Nat.le_succ i)]`. Simplify `this` using `[BlowupSequence.blowupMap]`. Establish `hiso : ∀ i, i ≤ s.length → IsIso (s.structMap i ∣_ I.support.compl)`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero`. Introduce `_`. Establish `: IsIso (s.structMap 0)` using `by rw [structMap_zero']; infer_instance`. Use `infer_instance`.

Consider the case `succ i ih`. Introduce `hi`. Establish `hlt : i < s.length` using `hi`. Establish `h2` using `ih hlt.le`. Establish `hb : Blowup.IsBlowupAlongIdealSheaf (s.blowupMap i) (s.center i)` using `s.isBlowup i hlt`.

Establish `hres` using `hb.restrict (s.structMap i ⁻¹ᵁ I.support.compl)`. Establish `htop : (s.center i).comap (s.structMap i ⁻¹ᵁ I.support.compl).ι = ⊤`. Apply `Blowup.comap_eq_top_of_notMem_support` to reduce the goal to its premises. Introduce `x hx`. Establish `h1` using `hsupp i hlt.le _ (hle i hlt |> Scheme.IdealSheafData.support_antitone <| hx)`.

Establish `hxV : (s.structMap i ⁻¹ᵁ I.support.compl).ι.base x ∈ ((s.structMap i ⁻¹ᵁ I.support.compl : (s.obj i).Opens) : Set (s.obj i))`. Rewrite using `[← Scheme.Opens.range_ι]`. Conclude with `Set.mem_range_self x`. Conclude with `hxV h1`. Rewrite `hres` using `[htop]`.

Establish `h1 : IsIso (s.blowupMap i ∣_ (s.structMap i ⁻¹ᵁ I.support.compl))` using `hres.isIso_of_top`. Establish `key` using `isIso_restrict_comp' (s.blowupMap i) (s.structMap i) I.support.compl h1 h2`. Establish `hcomp : s.blowupMap i ≫ s.structMap i = s.structMap (i + 1)` using `s.structMap_down (Nat.le_succ i)`. Rewrite `key` using `[hcomp]`. Conclude with `key`.

Conclude with `hiso s.length le_rfl`.
-/
theorem isIso_topMap_restrict_of_isPrincipalizingSequence {k : Type} [Field k] {X : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {E : List X.IdealSheafData} {s : BlowupSequence X}
    (h : IsPrincipalizingSequence p I E s) : IsIso (s.topMap ∣_ I.support.compl) := by
  obtain ⟨ideal, boundary, h0, -, -, -, hle, hsucc, -, -, -, -, -⟩ := h

  have hsupp : ∀ i, i ≤ s.length → ∀ x ∈ ((ideal i).support : Set (s.obj i)),
      (s.structMap i).base x ∈ (I.support : Set X) := by
    intro i
    induction i with
    | zero =>
      intro _ x hx
      rw [h0, Scheme.IdealSheafData.support_comap] at hx
      exact hx
    | succ i ih =>
      intro hi x hx
      have hlt : i < s.length := hi
      have e := congrArg Scheme.IdealSheafData.support (hsucc i hlt)
      rw [Scheme.IdealSheafData.support_mul] at e
      have hx' : x ∈ (((s.center i).comap (s.blowupMap i)).support ⊔ (ideal (i + 1)).support : Closeds _) :=
        Or.inr hx
      rw [e, Scheme.IdealSheafData.support_comap] at hx'
      have := ih hlt.le _ hx'
      rw [← s.structMap_down (Nat.le_succ i)]
      simpa [BlowupSequence.blowupMap] using this

  have hiso : ∀ i, i ≤ s.length → IsIso (s.structMap i ∣_ I.support.compl) := by
    intro i
    induction i with
    | zero =>
      intro _
      have : IsIso (s.structMap 0) := by rw [structMap_zero']; infer_instance
      infer_instance
    | succ i ih =>
      intro hi
      have hlt : i < s.length := hi
      have h2 := ih hlt.le
      have hb : Blowup.IsBlowupAlongIdealSheaf (s.blowupMap i) (s.center i) := s.isBlowup i hlt
      have hres := hb.restrict (s.structMap i ⁻¹ᵁ I.support.compl)
      have htop : (s.center i).comap (s.structMap i ⁻¹ᵁ I.support.compl).ι = ⊤ := by
        apply Blowup.comap_eq_top_of_notMem_support
        intro x hx
        have h1 := hsupp i hlt.le _ (hle i hlt |> Scheme.IdealSheafData.support_antitone <| hx)
        have hxV : (s.structMap i ⁻¹ᵁ I.support.compl).ι.base x
            ∈ ((s.structMap i ⁻¹ᵁ I.support.compl : (s.obj i).Opens) : Set (s.obj i)) := by
          rw [← Scheme.Opens.range_ι]
          exact Set.mem_range_self x
        exact hxV h1
      rw [htop] at hres
      have h1 : IsIso (s.blowupMap i ∣_ (s.structMap i ⁻¹ᵁ I.support.compl)) := hres.isIso_of_top
      have key := isIso_restrict_comp' (s.blowupMap i) (s.structMap i) I.support.compl h1 h2
      have hcomp : s.blowupMap i ≫ s.structMap i = s.structMap (i + 1) := s.structMap_down (Nat.le_succ i)
      rw [hcomp] at key
      exact key
  exact hiso s.length le_rfl

end PositivityTheory.ResPlug.FromRes
