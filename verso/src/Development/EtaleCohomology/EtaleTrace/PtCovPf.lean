import Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionConstantOnPointsOfConnected
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EtaleTrace

/- English proof (translation)
Use `hp` as an intermediate fact. Establish `: JacobsonSpace X` using `LocallyOfFiniteType.jacobsonSpace p`. Establish `hopen : IsOpen (Set.range f)` using `f.isOpenMap.isOpen_range`. Take `⟨y, ⟨x', rfl⟩, hy⟩` from `nonempty_inter_closedPoints (show (Set.range f).Nonempty from ⟨f x, x, rfl⟩) hopen.isLocallyClosed`. Set `s : S k ⟶ X` to `pointOfClosedPoint p (f x') hy`.

Take `⟨l, hl, -⟩` from `Scheme.exists_fac_of_etale_of_isSepClosed f s x' (pointOfClosedPoint_apply p (f x') hy _).symm`. Conclude with `⟨l, by rw [reassoc_of% hl]; exact pointOfClosedPoint_comp p (f x') hy⟩`.
-/
theorem exists_ratPt_of_etale (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ S k)
    (hp : IsProper p) {U : Scheme.{0}} (f : U ⟶ X) [Etale f] (x : U) :
    ∃ w : S k ⟶ U, w ≫ f ≫ p = 𝟙 _ := by
  have := hp
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have hopen : IsOpen (Set.range f) := f.isOpenMap.isOpen_range
  obtain ⟨y, ⟨x', rfl⟩, hy⟩ := nonempty_inter_closedPoints (show (Set.range f).Nonempty from ⟨f x, x, rfl⟩) hopen.isLocallyClosed
  let s : S k ⟶ X := pointOfClosedPoint p (f x') hy
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f s x' (pointOfClosedPoint_apply p (f x') hy _).symm
  exact ⟨l, by rw [reassoc_of% hl]; exact pointOfClosedPoint_comp p (f x') hy⟩

/- English proof (translation)
Introduce `k _ _ X p hp Sv hSv`. Take `⟨𝒰, h𝒰⟩` from `Scheme.mem_grothendieckTopology_iff.1 hSv`. Set `T : Sieve X` to `{ arrows := fun V g => ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U), Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _ downward_closed := by`. Introduce and unpack `V W g ⟨U, g', h, hg', rfl, w, hw⟩ a`. Conclude with `⟨U, g', a ≫ h, hg', by simp, w, hw⟩ }`.

Use `⟨T, ?_, fun V g hg => hg⟩` and prove the remaining obligations. Establish `hG : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ∈ Scheme.etaleTopology X` using `Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩`. Use `(Scheme.etaleTopology).transitive hG T ?_` and prove the remaining obligations. Introduce and unpack `Z _ ⟨W, a, b, hb, rfl⟩`. Rewrite using `[Sieve.pullback_comp]`.

Use `(Scheme.etaleTopology).pullback_stable a ?_` and prove the remaining obligations. Take `⟨i⟩` from `hb`. Distinguish the cases in `hne : Nonempty (𝒰.X i)`. Take `⟨x⟩` from `hne`. Take `⟨w, hw⟩` from `exists_ratPt_of_etale k p hp (𝒰.f i) x`.

Establish `: T.arrows (𝒰.f i)` using `⟨𝒰.X i, 𝒰.f i, 𝟙 _, h𝒰 _ _ (Presieve.ofArrows.mk i), by simp, w, hw⟩`. Rewrite using `[Sieve.pullback_eq_top_of_mem T this]`. Conclude with `(Scheme.etaleTopology).top_mem _`. Establish `: IsEmpty (𝒰.X i)` using `not_nonempty_iff.1 hne`. Conclude with `(Scheme.etaleTopology).superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)`.
-/
theorem PtCov_of : PtCov := by
  intro k _ _ X p hp Sv hSv
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.1 hSv
  let T : Sieve X :=
    { arrows := fun V g => ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U),
        Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _
      downward_closed := by
        rintro V W g ⟨U, g', h, hg', rfl, w, hw⟩ a
        exact ⟨U, g', a ≫ h, hg', by simp, w, hw⟩ }
  refine ⟨T, ?_, fun V g hg => hg⟩
  have hG : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ∈ Scheme.etaleTopology X :=
    Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩
  refine (Scheme.etaleTopology).transitive hG T ?_
  rintro Z _ ⟨W, a, b, hb, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable a ?_
  obtain ⟨i⟩ := hb
  by_cases hne : Nonempty (𝒰.X i)
  · obtain ⟨x⟩ := hne
    obtain ⟨w, hw⟩ := exists_ratPt_of_etale k p hp (𝒰.f i) x
    have : T.arrows (𝒰.f i) := ⟨𝒰.X i, 𝒰.f i, 𝟙 _, h𝒰 _ _ (Presieve.ofArrows.mk i), by simp, w, hw⟩
    rw [Sieve.pullback_eq_top_of_mem T this]
    exact (Scheme.etaleTopology).top_mem _
  · have : IsEmpty (𝒰.X i) := not_nonempty_iff.1 hne
    exact (Scheme.etaleTopology).superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)

end LateralTheory.EtaleTrace
