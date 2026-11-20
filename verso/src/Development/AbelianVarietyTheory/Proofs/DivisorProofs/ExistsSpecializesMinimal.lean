import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.FinAffAmple

variable {X : Scheme.{0}} {M : LB X}

/- English proof (translation)
Distinguish the cases in `hc : ∃ k, x ∈ M.U k`. Take `⟨k, hk⟩` from `hc`. Rewrite `*` using `[GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk, GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk]`. Express the relevant statement in the definitionally equal form `x ∈ X.basicOpen (s.f k + t.f k) ↔ _`. Rewrite `*` using `[Scheme.mem_basicOpen _ _ _ hk, Scheme.mem_basicOpen _ _ _ hk]`.

Rewrite using `[map_add]`. Establish `hm : (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (t.f k) ∈ IsLocalRing.maximalIdeal _` using `(IsLocalRing.mem_maximalIdeal _).2 ht`. Use `Ideal.add_mem_iff_left (IsLocalRing.maximalIdeal _) (a := (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (s.f k)) hm` as an intermediate fact. Rewrite `this` using `[IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]`. Conclude with `not_iff_not.1 this`.

Use `push_neg at hc`. Conclude with `⟨fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc), fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc)⟩`.
-/
theorem mem_secAdd_iff_right {s t : M.Sec} {x : X} (ht : x ∉ nonzeroLocus t) :
    x ∈ nonzeroLocus (DVR.SecOps.secAdd s t) ↔ x ∈ nonzeroLocus s := by
  by_cases hc : ∃ k, x ∈ M.U k
  · obtain ⟨k, hk⟩ := hc
    rw [GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk, GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk] at *
    change x ∈ X.basicOpen (s.f k + t.f k) ↔ _
    rw [Scheme.mem_basicOpen _ _ _ hk, Scheme.mem_basicOpen _ _ _ hk] at *
    rw [map_add]
    have hm : (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (t.f k) ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).2 ht
    have := Ideal.add_mem_iff_left (IsLocalRing.maximalIdeal _)
      (a := (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (s.f k)) hm
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff] at this
    exact not_iff_not.1 this
  · push_neg at hc
    exact ⟨fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc),
      fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc)⟩

/- English proof (translation)
Establish `e : DVR.SecOps.secAdd s t = DVR.SecOps.secAdd t s` using `DVR.SecOps.sec_ext fun i => add_comm (s.f i) (t.f i)`. Rewrite using `[e]`. Conclude with `mem_secAdd_iff_right hs`.
-/
theorem mem_secAdd_iff_left {s t : M.Sec} {x : X} (hs : x ∉ nonzeroLocus s) :
    x ∈ nonzeroLocus (DVR.SecOps.secAdd s t) ↔ x ∈ nonzeroLocus t := by
  have e : DVR.SecOps.secAdd s t = DVR.SecOps.secAdd t s := DVR.SecOps.sec_ext fun i => add_comm (s.f i) (t.f i)
  rw [e]
  exact mem_secAdd_iff_right hs

/- English proof (translation)
It suffices to establish `H : ∀ T' : Finset X, T' ⊆ T → ∃ g : M.Sec, ∀ x ∈ T, (x ∈ nonzeroLocus g ↔ x ∈ T') by`. Take `⟨g, hg⟩` from `H T subset_rfl`. Conclude with `⟨g, fun x hx => (hg x hx).2 hx⟩`. Introduce `T'`. Proceed by induction on `T' using Finset.induction_on with`.

Consider the case `empty`. Introduce `_`. Use `⟨DVR.SecOps.secZero, fun x _ => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.nonzeroLocus_secZero]`. Simplify using the standard rewrite rules.

Consider the case `insert a T' ha ih`. Introduce `hsub`. Take `⟨g, hg⟩` from `ih ((Finset.subset_insert a T').trans hsub)`. Establish `haT : a ∈ T` using `hsub (Finset.mem_insert_self a T')`. Use `⟨DVR.SecOps.secAdd g (t a), fun x hx => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hxa : x = a`. Substitute `hxa` using the available equality. Rewrite using `[mem_secAdd_iff_left (fun h => ha ((hg x hx).1 h))]`. Simplify using `using ht x haT`. Rewrite using `[mem_secAdd_iff_right (ht' a haT x hx hxa), hg x hx, Finset.mem_insert]`.

Simplify using `[hxa]`.
-/
theorem exists_sec_forall_mem (T : Finset X) (t : X → M.Sec) (ht : ∀ x ∈ T, x ∈ nonzeroLocus (t x))
    (ht' : ∀ x ∈ T, ∀ y ∈ T, y ≠ x → y ∉ nonzeroLocus (t x)) :
    ∃ g : M.Sec, ∀ x ∈ T, x ∈ nonzeroLocus g := by
  classical
  suffices H : ∀ T' : Finset X, T' ⊆ T → ∃ g : M.Sec, ∀ x ∈ T, (x ∈ nonzeroLocus g ↔ x ∈ T') by
    obtain ⟨g, hg⟩ := H T subset_rfl
    exact ⟨g, fun x hx => (hg x hx).2 hx⟩
  intro T'
  induction T' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨DVR.SecOps.secZero, fun x _ => ?_⟩
    rw [GlobalTheory.nonzeroLocus_secZero]
    simp
  | insert a T' ha ih =>
    intro hsub
    obtain ⟨g, hg⟩ := ih ((Finset.subset_insert a T').trans hsub)
    have haT : a ∈ T := hsub (Finset.mem_insert_self a T')
    refine ⟨DVR.SecOps.secAdd g (t a), fun x hx => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      rw [mem_secAdd_iff_left (fun h => ha ((hg x hx).1 h))]
      simpa using ht x haT
    · rw [mem_secAdd_iff_right (ht' a haT x hx hxa), hg x hx, Finset.mem_insert]
      simp [hxa]

/- English proof (translation)
Take `⟨y, hy, hmin⟩` from `Finset.exists_min_image (F.filter (x ⤳ ·)) (fun y => (F.filter (y ⤳ ·)).card) ⟨x, Finset.mem_filter.2 ⟨hx, specializes_refl x⟩⟩`. Take `⟨hyF, hxy⟩` from `Finset.mem_filter.1 hy`. Use `⟨y, hyF, hxy, fun z hz hyz => ?_⟩` and prove the remaining obligations. Establish `hsub : F.filter (z ⤳ ·) ⊆ F.filter (y ⤳ ·)` using `fun w hw => by`. Take `⟨hwF, hzw⟩` from `Finset.mem_filter.1 hw`.

Conclude with `Finset.mem_filter.2 ⟨hwF, hyz.trans hzw⟩`. Establish `hle` using `hmin z (Finset.mem_filter.2 ⟨hz, hxy.trans hyz⟩)`. Establish `heq` using `Finset.eq_of_subset_of_card_le hsub hle`. Establish `hzy : z ⤳ y` using `(Finset.mem_filter.1 (heq ▸ Finset.mem_filter.2 ⟨hyF, specializes_refl y⟩ : y ∈ F.filter (z ⤳ ·))).2`. Conclude with `(hyz.antisymm hzy).eq.symm`.
-/
theorem exists_specializes_minimal {Z : Type*} [TopologicalSpace Z] [T0Space Z] (F : Finset Z) {x : Z}
    (hx : x ∈ F) : ∃ y ∈ F, x ⤳ y ∧ ∀ z ∈ F, y ⤳ z → z = y := by
  classical
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image (F.filter (x ⤳ ·)) (fun y => (F.filter (y ⤳ ·)).card)
    ⟨x, Finset.mem_filter.2 ⟨hx, specializes_refl x⟩⟩
  obtain ⟨hyF, hxy⟩ := Finset.mem_filter.1 hy
  refine ⟨y, hyF, hxy, fun z hz hyz => ?_⟩
  have hsub : F.filter (z ⤳ ·) ⊆ F.filter (y ⤳ ·) := fun w hw => by
    obtain ⟨hwF, hzw⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hwF, hyz.trans hzw⟩
  have hle := hmin z (Finset.mem_filter.2 ⟨hz, hxy.trans hyz⟩)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hzy : z ⤳ y := (Finset.mem_filter.1 (heq ▸ Finset.mem_filter.2 ⟨hyF, specializes_refl y⟩ :
    y ∈ F.filter (z ⤳ ·))).2
  exact (hyz.antisymm hzy).eq.symm

/- English proof (translation)
Introduce `F`. Set `F'` to `F.filter (fun x => ∀ z ∈ F, x ⤳ z → z = x)`. Set `V : X → X.Opens` to `fun x => ⟨(⋃ y ∈ F'.erase x, closure ({y} : Set X))ᶜ, (isClosed_biUnion_finset fun _ _ => isClosed_closure).isOpen_compl⟩`. Establish `hV : ∀ x ∈ F', x ∈ V x`. Introduce `x hx hmem`.

Take `⟨y, hy, hxy⟩` from `Set.mem_iUnion₂.1 hmem`. Take `⟨hyx, hyF'⟩` from `Finset.mem_erase.1 hy`. Establish `hyx' : y ⤳ x` using `specializes_iff_mem_closure.2 hxy`. Conclude with `hyx ((Finset.mem_filter.1 hyF').2 x (Finset.mem_filter.1 hx).1 hyx').symm`. Establish `hV' : ∀ x ∈ F', ∀ y ∈ F', y ≠ x → y ∉ V x` using `fun x _ y hy hyx hmem => hmem (Set.mem_iUnion₂.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, subset_closure rfl⟩)`.

Use `choose n hn s hs hsV _ using fun x : F' => h.exists_affine_le (hV x.1 x.2)`. Take `⟨N, hN, t, ht⟩` from `exists_common_pow n hn s`. Set `tt : X → (lbPow L N).Sec` to `fun x => if hx : x ∈ F' then t ⟨x, hx⟩ else DVR.SecOps.secZero`. Establish `htt : ∀ x (hx : x ∈ F'), nonzeroLocus (tt x) = nonzeroLocus (s ⟨x, hx⟩)` using `fun x hx => by`. Simplify using `only [tt, dif_pos hx, ht]`.

Take `⟨g, hg⟩` from `exists_sec_forall_mem F' tt (fun x hx => (htt x hx).symm ▸ hs ⟨x, hx⟩) (fun x hx y hy hyx hmem => hV' x hx y hy hyx (hsV ⟨x, hx⟩ ((htt x hx) ▸ hmem)))`. Use `⟨nonzeroLocus g, h.isAffineOpen_nonzeroLocus f hN g, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hyF, hxy, hmin⟩` from `exists_specializes_minimal F hx`. Conclude with `hxy.mem_open (nonzeroLocus g).isOpen (hg y (Finset.mem_filter.2 ⟨hyF, hmin⟩))`.
-/
theorem finAff_of_isAmpleLB {Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f] {L : LB X}
    (h : IsAmpleLB L) : FinAff X := by
  classical
  intro F
  let F' := F.filter (fun x => ∀ z ∈ F, x ⤳ z → z = x)
  let V : X → X.Opens := fun x =>
    ⟨(⋃ y ∈ F'.erase x, closure ({y} : Set X))ᶜ, (isClosed_biUnion_finset fun _ _ => isClosed_closure).isOpen_compl⟩
  have hV : ∀ x ∈ F', x ∈ V x := by
    intro x hx hmem
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hmem
    obtain ⟨hyx, hyF'⟩ := Finset.mem_erase.1 hy
    have hyx' : y ⤳ x := specializes_iff_mem_closure.2 hxy
    exact hyx ((Finset.mem_filter.1 hyF').2 x (Finset.mem_filter.1 hx).1 hyx').symm
  have hV' : ∀ x ∈ F', ∀ y ∈ F', y ≠ x → y ∉ V x := fun x _ y hy hyx hmem =>
    hmem (Set.mem_iUnion₂.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, subset_closure rfl⟩)
  choose n hn s hs hsV _ using fun x : F' => h.exists_affine_le (hV x.1 x.2)
  obtain ⟨N, hN, t, ht⟩ := exists_common_pow n hn s
  let tt : X → (lbPow L N).Sec := fun x => if hx : x ∈ F' then t ⟨x, hx⟩ else DVR.SecOps.secZero
  have htt : ∀ x (hx : x ∈ F'), nonzeroLocus (tt x) = nonzeroLocus (s ⟨x, hx⟩) := fun x hx => by
    simp only [tt, dif_pos hx, ht]
  obtain ⟨g, hg⟩ := exists_sec_forall_mem F' tt (fun x hx => (htt x hx).symm ▸ hs ⟨x, hx⟩)
    (fun x hx y hy hyx hmem => hV' x hx y hy hyx (hsV ⟨x, hx⟩ ((htt x hx) ▸ hmem)))
  refine ⟨nonzeroLocus g, h.isAffineOpen_nonzeroLocus f hN g, fun x hx => ?_⟩
  obtain ⟨y, hyF, hxy, hmin⟩ := exists_specializes_minimal F hx
  exact hxy.mem_open (nonzeroLocus g).isOpen (hg y (Finset.mem_filter.2 ⟨hyF, hmin⟩))

/- English proof (translation)
Introduce `R _ B _ hB L hL hA`. Use `hB.proper` as an intermediate fact. Conclude with `finAff_of_isAmpleLB B.hom (isAmpleLB_of_relAmple_of_isAffine B hL hA)`.
-/
theorem finAff_of_relAmple : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
    ∀ L : LB B.left, L.IsLB → Out.RelAmple B L → FinAff B.left := by
  intro R _ B _ hB L hL hA
  have := hB.proper
  exact finAff_of_isAmpleLB B.hom (isAmpleLB_of_relAmple_of_isAffine B hL hA)

end GlobalTheory.DualCon.FinAffAmple
