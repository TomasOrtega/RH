import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.FrobTraceOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

/- English proof (translation)
Rewrite using `[LateralTheory.EtaleTrace.pb_comp]`. Both sides reduce to the same expression.
-/
private theorem pbc (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) (z : V l C n) :
    pb l (f ≫ g) n z = pb l f n (pb l g n z) := by
  rw [LateralTheory.EtaleTrace.pb_comp]; rfl

/- English proof (translation)
Use `show pullHQ l (sch.map (𝟙 X)) n 0 z = z`. Rewrite using `[CategoryTheory.Functor.map_id]`. Unfold `pullHQ`. Rewrite using `[pullHl_id, LinearMap.baseChange_id]`. Both sides reduce to the same expression.
-/
private theorem pbi (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (z : V l X n) : pb l (𝟙 X) n z = z := by
  show pullHQ l (sch.map (𝟙 X)) n 0 z = z
  rw [CategoryTheory.Functor.map_id]
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]; rfl

/- English proof (translation)
Establish `hsep : IsSeparated (U'.ι ≫ p)` using `inferInstance`. Establish `hsm' : SmoothOfRelativeDimension d (U'.ι ≫ p)`. Establish `h` using `smoothOfRelativeDimension_comp (n := 0) (m := d) U'.ι p`. Rewrite `h` using `[Nat.zero_add]`. Then use the resulting hypothesis. Establish `hr : Set.range y.1 ⊆ Set.range U'.ι` using `by simpa using hy`.

Set `y' : S k ⟶ U'.toScheme` to `IsOpenImmersion.lift U'.ι y.1 hr`. Establish `hy' : y' ≫ U'.ι = y.1` using `IsOpenImmersion.lift_fac _ _ _`. Set `t : Pt (U'.ι ≫ p)` to `⟨y', by rw [← Category.assoc, hy', y.2]⟩`. Establish `hpt : IsPair d 0 (U'.ι ≫ p) y'` using `((hP k d _ hsep hsm').2 t).1`. Establish `hpy : IsPair d 0 p y.1` using `((hP k d p hs hsm).2 y).1`.

Establish `hoff : Off y' (U'.ι ⁻¹ᵁ U)`. Unfold `Off`. Use extensionality with `x`. Establish `hx : U'.ι x ∈ (U' : Set X)`. Establish `: U'.ι x ∈ Set.range U'.ι` using `⟨x, rfl⟩`.

Simplify using `using this`. Use `show U'.ι x ∈ (U : Set X) ↔ x ∉ Set.range y'`. Rewrite using `[hU]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h2⟩ ⟨w, rfl⟩`.

Conclude with `h2 ⟨w, by rw [← hy']; rfl⟩`. Introduce `h`. Use `⟨hx, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨w, hw⟩`. Apply `h` to reduce the goal to its premises.

Use `⟨w, ?_⟩` and prove the remaining obligations. Apply `U'.ι.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[← hw, ← hy']`. Both sides reduce to the same expression. Establish `hdead : pb l (U'.ι ⁻¹ᵁ U).ι _ (pb l U'.ι _ z) = 0`.

Rewrite using `[← pbc, ← morphismRestrict_ι, pbc, hz, map_zero]`. Establish `hprop : IsProper (y' ≫ U'.ι ≫ p)`. Establish `: y' ≫ U'.ι ≫ p = 𝟙 _` using `t.2`. Rewrite using `[this]`. Use `infer_instance`.

Take `⟨a, ha⟩` from `G.onto hpt (zero_add _) _ hoff hprop _ hdead`. Take `⟨r, hra, -⟩` from `hL.line a`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `hpb : IsPullback y' (𝟙 _) U'.ι y.1` using `IsPullback.of_vert_isIso_mono ⟨by simp [hy']⟩`. Establish `hnat` using `G.nat hpt hpy U'.ι (𝟙 _) rfl hpb (zero_add _) (oneV l (S k))`.

Rewrite `hnat` using `[pbi]`. Establish `hpt' : G.pt d y = G.g hpy (zero_add _) (oneV l (S k))`. Simplify using `only [GysQ.cls, dif_pos hpy]`. Rewrite using `[map_sub, map_smul, hpt', hnat, ← map_smul, ← hra, ha, sub_self]`.
-/
private theorem step {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (hP : Pairs) (hL : Low l k) (G : GysQ k l) (d : ℕ)
    {X : Scheme.{0}} (p : X ⟶ S k) (hs : IsSeparated p) (hsm : SmoothOfRelativeDimension d p) (y : Pt p)
    (U' U : X.Opens) (hU : (U : Set X) = (U' : Set X) \ Set.range y.1) (hy : Set.range y.1 ⊆ (U' : Set X))
    (z : V l X (2 * d)) (hz : pb l U.ι _ z = 0) :
    ∃ r : ℚ_[l], pb l U'.ι _ (z - r • G.pt d y) = 0 := by
  have hsep : IsSeparated (U'.ι ≫ p) := inferInstance
  have hsm' : SmoothOfRelativeDimension d (U'.ι ≫ p) := by
    have h := smoothOfRelativeDimension_comp (n := 0) (m := d) U'.ι p
    rwa [Nat.zero_add] at h
  have hr : Set.range y.1 ⊆ Set.range U'.ι := by simpa using hy
  let y' : S k ⟶ U'.toScheme := IsOpenImmersion.lift U'.ι y.1 hr
  have hy' : y' ≫ U'.ι = y.1 := IsOpenImmersion.lift_fac _ _ _
  let t : Pt (U'.ι ≫ p) := ⟨y', by rw [← Category.assoc, hy', y.2]⟩
  have hpt : IsPair d 0 (U'.ι ≫ p) y' := ((hP k d _ hsep hsm').2 t).1
  have hpy : IsPair d 0 p y.1 := ((hP k d p hs hsm).2 y).1
  have hoff : Off y' (U'.ι ⁻¹ᵁ U) := by
    unfold Off
    ext x
    have hx : U'.ι x ∈ (U' : Set X) := by
      have : U'.ι x ∈ Set.range U'.ι := ⟨x, rfl⟩
      simpa using this
    show U'.ι x ∈ (U : Set X) ↔ x ∉ Set.range y'
    rw [hU]
    constructor
    · rintro ⟨-, h2⟩ ⟨w, rfl⟩
      exact h2 ⟨w, by rw [← hy']; rfl⟩
    · intro h
      refine ⟨hx, ?_⟩
      rintro ⟨w, hw⟩
      apply h
      refine ⟨w, ?_⟩
      apply U'.ι.isOpenEmbedding.injective
      rw [← hw, ← hy']; rfl
  have hdead : pb l (U'.ι ⁻¹ᵁ U).ι _ (pb l U'.ι _ z) = 0 := by
    rw [← pbc, ← morphismRestrict_ι, pbc, hz, map_zero]
  have hprop : IsProper (y' ≫ U'.ι ≫ p) := by
    have : y' ≫ U'.ι ≫ p = 𝟙 _ := t.2
    rw [this]; infer_instance
  obtain ⟨a, ha⟩ := G.onto hpt (zero_add _) _ hoff hprop _ hdead
  obtain ⟨r, hra, -⟩ := hL.line a
  refine ⟨r, ?_⟩
  have hpb : IsPullback y' (𝟙 _) U'.ι y.1 := IsPullback.of_vert_isIso_mono ⟨by simp [hy']⟩
  have hnat := G.nat hpt hpy U'.ι (𝟙 _) rfl hpb (zero_add _) (oneV l (S k))
  rw [pbi] at hnat
  have hpt' : G.pt d y = G.g hpy (zero_add _) (oneV l (S k)) := by
    simp only [GysQ.cls, dif_pos hpy]
  rw [map_sub, map_smul, hpt', hnat, ← map_smul, ← hra, ha, sub_self]

end UpperTheory.Gal.KunnethLefschetz

/- English proof (translation)
Unfold `FinSupp`. Introduce `_ hP l _ k _ _ _ _ hL G d X p hsep hsm s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `U hU z hz`.

Establish `hT : U = ⊤`. Apply `SetLike.coe_injective` to reduce the goal to its premises. Simplify `hU` using `[OffPts]`. Substitute `hT` using the available equality. Establish `h0 : z = 0`.

Establish `e : X.topIso.inv ≫ (⊤ : X.Opens).ι = 𝟙 X` using `by simp`. Establish `h1 : pb l X.topIso.inv _ (pb l (⊤ : X.Opens).ι _ z) = z`. Rewrite using `[← pbc, e, pbi]`. Rewrite using `[← h1, hz, map_zero]`. Rewrite using `[h0]`.

Conclude with `zero_mem _`. Consider the case `insert y s hy ih`. Introduce `U hU z hz`. Establish `hcl : ∀ t : Pt p, IsClosed (Set.range t.1)` using `fun t => by haveI := ((hP k d p hsep hsm).2 t).1.cl`. Conclude with `t.1.isClosedEmbedding.isClosed_range`.

Establish `hopen : IsOpen ((⋃ t ∈ s, Set.range t.1)ᶜ)` using `(s.finite_toSet.isClosed_biUnion fun t _ => hcl t).isOpen_compl`. Set `U' : X.Opens` to `⟨_, hopen⟩`. Establish `hU' : OffPts s U'` using `rfl`. Establish `hU2 : (U : Set X) = (U' : Set X) \ Set.range y.1`. Rewrite using `[hU, Finset.set_biUnion_insert, Set.compl_union, Set.diff_eq, Set.inter_comm]`.

Both sides reduce to the same expression. Distinguish the cases in `hin : Set.range y.1 ⊆ (U' : Set X)`. Take `⟨r, hr⟩` from `step hP hL G d p hsep hsm y U' U hU2 hin z hz`. Establish `h1` using `ih U' hU' _ hr`. Establish `hz' : z = (z - r • G.pt d y) + r • G.pt d y` using `(sub_add_cancel _ _).symm`.

Rewrite using `[hz']`. Conclude with `add_mem h1 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩))`. Establish `hsub : Subsingleton (S k)` using `inferInstanceAs (Subsingleton (PrimeSpectrum k))`. Establish `hUU : U = U'`. Apply `SetLike.coe_injective` to reduce the goal to its premises.

Rewrite using `[hU2]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`. Introduce `hx`.

Use `⟨hx, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨w, rfl⟩`. Apply `hin` to reduce the goal to its premises. Introduce and unpack `_ ⟨w', rfl⟩`. Rewrite using `[Subsingleton.elim w' w]` and apply the resulting hypothesis.

Substitute `hUU` using the available equality. Conclude with `ih _ hU' z hz`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.finSupp_holds :
    UpperTheory.Gal.KunnethLefschetz.FinSupp := by
  unfold FinSupp
  intro _ hP l _ k _ _ _ _ hL G d X p hsep hsm s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro U hU z hz
    have hT : U = ⊤ := by
      apply SetLike.coe_injective
      simpa [OffPts] using hU
    subst hT
    have h0 : z = 0 := by
      have e : X.topIso.inv ≫ (⊤ : X.Opens).ι = 𝟙 X := by simp
      have h1 : pb l X.topIso.inv _ (pb l (⊤ : X.Opens).ι _ z) = z := by
        rw [← pbc, e, pbi]
      rw [← h1, hz, map_zero]
    rw [h0]; exact zero_mem _
  | insert y s hy ih =>
    intro U hU z hz
    have hcl : ∀ t : Pt p, IsClosed (Set.range t.1) := fun t => by
      haveI := ((hP k d p hsep hsm).2 t).1.cl
      exact t.1.isClosedEmbedding.isClosed_range
    have hopen : IsOpen ((⋃ t ∈ s, Set.range t.1)ᶜ) :=
      (s.finite_toSet.isClosed_biUnion fun t _ => hcl t).isOpen_compl
    let U' : X.Opens := ⟨_, hopen⟩
    have hU' : OffPts s U' := rfl
    have hU2 : (U : Set X) = (U' : Set X) \ Set.range y.1 := by
      rw [hU, Finset.set_biUnion_insert, Set.compl_union, Set.diff_eq, Set.inter_comm]; rfl
    by_cases hin : Set.range y.1 ⊆ (U' : Set X)
    · obtain ⟨r, hr⟩ := step hP hL G d p hsep hsm y U' U hU2 hin z hz
      have h1 := ih U' hU' _ hr
      have hz' : z = (z - r • G.pt d y) + r • G.pt d y := (sub_add_cancel _ _).symm
      rw [hz']
      exact add_mem h1 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩))
    · have hsub : Subsingleton (S k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
      have hUU : U = U' := by
        apply SetLike.coe_injective
        rw [hU2]
        ext x
        constructor
        · exact fun h => h.1
        · intro hx
          refine ⟨hx, ?_⟩
          rintro ⟨w, rfl⟩
          apply hin
          rintro _ ⟨w', rfl⟩
          rwa [Subsingleton.elim w' w]
      subst hUU
      exact ih _ hU' z hz
