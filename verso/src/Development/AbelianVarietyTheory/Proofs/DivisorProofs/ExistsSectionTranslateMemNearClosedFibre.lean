import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGroupSectionsDenseInFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MoveNear

/- English proof (translation)
Introduce `R _ _ _ hR S π G' _ _ _ N e he hPt Ω _ s g hT hs`. Use `haveI := N.isOpen`. Use `haveI := hR.1`. Set `xR` to `s ≫ π`. Set `UΩ` to `pullback N.U.hom xR`.

Set `T` to `pullback G'.hom s`. Set `m : UΩ ⟶ pullback N.U.hom π` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s) (by rw [Category.assoc]; exact pullback.condition)`. Set `k : UΩ ⟶ T` to `pullback.lift (m ≫ N.u) (pullback.snd _ _) (by rw [Category.assoc, N.u_over, pullback.lift_snd])`. Establish `sqP : IsPullback m (pullback.snd N.U.hom xR) (pullback.snd N.U.hom π) s`. Use `IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback N.U.hom π)` and prove the remaining obligations.

Rewrite using `[pullback.lift_fst]`. Conclude with `IsPullback.of_hasPullback N.U.hom xR`. Establish `sqk : IsPullback m k N.u (pullback.fst G'.hom s)`. Use `IsPullback.of_bot (v₂₁ := pullback.snd G'.hom s) (v₂₂ := G'.hom) (h₃₁ := s) ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback G'.hom s)` and prove the remaining obligations. Rewrite using `[pullback.lift_snd, N.u_over]`.

Conclude with `sqP`. Establish `hk : IsOpenImmersion k` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqk N.isOpen`. Set `TO : Over S` to `Over.mk (pullback.snd G'.hom s ≫ s)`. Set `yT : TO ⟶ G'` to `Over.homMk (pullback.fst G'.hom s) pullback.condition`. Set `qT : TO ⟶ Over.mk s` to `Over.homMk (pullback.snd G'.hom s) rfl`.

Set `zT : TO ⟶ G'` to `(qT ≫ g) * yT`. Set `UO : Over S` to `Over.mk (pullback.snd N.U.hom xR ≫ s)`. Set `kO : UO ⟶ TO` to `Over.homMk k (by`. Express the relevant statement in the definitionally equal form `k ≫ pullback.snd _ _ ≫ s = _`. Rewrite using `[pullback.lift_snd_assoc]`.

Use the proof step `rfl)`. Establish `sec : ∀ h : Over.mk s ⟶ G', ∃ σ : Over.mk s ⟶ TO, σ ≫ yT = h ∧ σ ≫ qT = 𝟙 _` using `fun h => ⟨Over.homMk (pullback.lift h.left (𝟙 _) ((Over.w h).trans (Category.id_comp _).symm)) (by`. Express the relevant statement in the definitionally equal form `pullback.lift _ _ _ ≫ pullback.snd G'.hom s ≫ s = s`. Rewrite using `[pullback.lift_snd_assoc]`. Conclude with `Category.id_comp _),`.

Use the proof step `Over.OverMorphism.ext (pullback.lift_fst _ _ _), Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩`. Establish `hone : ∀ p, (1 : Over.mk s ⟶ G').left p ∈ Set.range N.u`. Take `⟨x₀, -, -, hx₀⟩` from `hPt`. Establish `e₁ : (1 : Over.mk s ⟶ G').left = s ≫ (1 : Over.mk (𝟙 S) ⟶ G').left` using `congrArg (fun f => f.left) (MonObj.comp_one (M := G') (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S))).symm`. Introduce `p`.

Rewrite using `[e₁, ← hx₀]`. Conclude with `⟨x₀ (s p), rfl⟩`. Establish `hoU : IsOpen (Set.range N.u)` using `N.u.isOpenEmbedding.isOpen_range`. Take `⟨σ₁, h₁, -⟩` from `sec 1`. Take `⟨σ₂, h₂, h₂'⟩` from `sec g⁻¹`.

Establish `e₂ : σ₂ ≫ zT = 1`. Rewrite using `[MonObj.comp_mul, h₂, ← Category.assoc, h₂', Category.id_comp, mul_inv_cancel]`. Establish `: IrreducibleSpace T` using `hT`. Take `⟨t, ⟨p₀, hp₀⟩, ht⟩` from `nonempty_preirreducible_inter (hoU.preimage (pullback.fst G'.hom s).continuous) (hoU.preimage zT.left.continuous) ⟨σ₁.left (IsLocalRing.closedPoint _), by`. Use `hone (IsLocalRing.closedPoint _)` as an intermediate fact.

Rewrite `this` using `[← h₁]`. Conclude with `this⟩`. Use the proof step `⟨σ₂.left (IsLocalRing.closedPoint _), by`. Use `hone (IsLocalRing.closedPoint _)` as an intermediate fact. Rewrite `this` using `[← e₂]`.

Conclude with `this⟩`. Take `⟨w, -, hw⟩` from `Scheme.exists_preimage_of_isPullback sqk p₀ t hp₀`. Set `O : UΩ.Opens` to `⟨(kO ≫ zT).left ⁻¹' Set.range N.u, hoU.preimage (kO ≫ zT).left.continuous⟩`. Establish `hwO : w ∈ O` using `by show (kO ≫ zT).left w ∈ Set.range N.u`. Rewrite using `[Over.comp_left, Scheme.Hom.comp_apply]`.

Express the relevant statement in the definitionally equal form `zT.left (k w) ∈ Set.range N.u`. Rewrite using `[hw]`. Conclude with `ht`. Establish `hirr : IrreducibleSpace UΩ`. Use `(irreducibleSpace_def _).2 ⟨⟨w, trivial⟩, ?_⟩` and prove the remaining obligations.

Use `(IrreducibleSpace.isIrreducible_univ T).2.preimage k.isOpenEmbedding` as an intermediate fact. Simplify using `using this`. Take `⟨a, aΩ, ha, haf, has, hao⟩` from `GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hR.2.2.2 N.U N.smooth e he Ω xR hs hirr O ⟨w, hwO⟩`. Set `x : Over.mk (𝟙 S) ⟶ G'` to `Over.homMk (pullback.lift (π ≫ a) (𝟙 S) (by rw [Category.assoc, ha, Category.comp_id]; exact (Category.id_comp π).symm) ≫ N.u) (by rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)`. Use `⟨a, x, ha, ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, ?_⟩` and prove the remaining obligations.

Set `rO : Over.mk s ⟶ UO` to `Over.homMk aΩ (by`. Express the relevant statement in the definitionally equal form `aΩ ≫ pullback.snd _ _ ≫ s = s`. Rewrite using `[← Category.assoc, has, Category.id_comp])`. Establish `hq : rO ≫ kO ≫ qT = 𝟙 _`. Use `ext`.

Express the relevant statement in the definitionally equal form `aΩ ≫ k ≫ pullback.snd _ _ = 𝟙 _`. Rewrite using `[pullback.lift_snd, has]`. Establish `hy : rO ≫ kO ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x`. Use `ext`. Express the relevant statement in the definitionally equal form `aΩ ≫ k ≫ pullback.fst _ _ = s ≫ pullback.lift (π ≫ a) (𝟙 S) _ ≫ N.u`.

Rewrite using `[pullback.lift_fst, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, pullback.lift_fst] show aΩ ≫ pullback.lift (pullback.fst N.U.hom xR) _ _ ≫ pullback.fst N.U.hom π = s ≫ π ≫ a`. Rewrite using `[pullback.lift_fst, haf]`.

Simplify using `only [xR, Category.assoc]`. Rewrite using `[Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, has, Category.id_comp, Category.comp_id]`. Establish `hz : g * ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x) = rO ≫ kO ≫ zT`. Establish `hq' : (rO ≫ kO) ≫ qT = 𝟙 _` using `by rw [Category.assoc]; exact hq`. Establish `hy' : (rO ≫ kO) ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x`.

Rewrite using `[Category.assoc]`. Conclude with `hy`. Rewrite using `[← Category.assoc, MonObj.comp_mul, ← Category.assoc, hq', Category.id_comp, hy']`. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[hz]`.

Conclude with `hao ⟨p, rfl⟩`.
-/
theorem exists_section_translate_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (N : Near π G') (e : Sp R ⟶ N.U.left), e ≫ N.U.hom = 𝟙 _ → N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left → ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), IrreducibleSpace (pullback G'.hom s : Scheme.{0}) → closedPoint R ∉ Set.range (s ≫ π) → ∃ (a : Sp R ⟶ N.U.left) (x : Over.mk (𝟙 S) ⟶ G'), a ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a) x.left ∧ Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left ⊆ Set.range N.u := by
  intro R _ _ _ hR S π G' _ _ _ N e he hPt Ω _ s g hT hs
  haveI := N.isOpen
  haveI := hR.1
  let xR := s ≫ π
  let UΩ := pullback N.U.hom xR
  let T := pullback G'.hom s
  let m : UΩ ⟶ pullback N.U.hom π := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [Category.assoc]; exact pullback.condition)
  let k : UΩ ⟶ T := pullback.lift (m ≫ N.u) (pullback.snd _ _)
    (by rw [Category.assoc, N.u_over, pullback.lift_snd])
  have sqP : IsPullback m (pullback.snd N.U.hom xR) (pullback.snd N.U.hom π) s := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback N.U.hom π)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback N.U.hom xR
  have sqk : IsPullback m k N.u (pullback.fst G'.hom s) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd G'.hom s) (v₂₂ := G'.hom) (h₃₁ := s) ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback G'.hom s)
    rw [pullback.lift_snd, N.u_over]
    exact sqP
  have hk : IsOpenImmersion k := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqk N.isOpen
  let TO : Over S := Over.mk (pullback.snd G'.hom s ≫ s)
  let yT : TO ⟶ G' := Over.homMk (pullback.fst G'.hom s) pullback.condition
  let qT : TO ⟶ Over.mk s := Over.homMk (pullback.snd G'.hom s) rfl
  let zT : TO ⟶ G' := (qT ≫ g) * yT
  let UO : Over S := Over.mk (pullback.snd N.U.hom xR ≫ s)
  let kO : UO ⟶ TO := Over.homMk k (by
    change k ≫ pullback.snd _ _ ≫ s = _
    rw [pullback.lift_snd_assoc]
    rfl)
  have sec : ∀ h : Over.mk s ⟶ G', ∃ σ : Over.mk s ⟶ TO, σ ≫ yT = h ∧ σ ≫ qT = 𝟙 _ := fun h =>
    ⟨Over.homMk (pullback.lift h.left (𝟙 _) ((Over.w h).trans (Category.id_comp _).symm))
      (by
        change pullback.lift _ _ _ ≫ pullback.snd G'.hom s ≫ s = s
        rw [pullback.lift_snd_assoc]
        exact Category.id_comp _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _), Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩
  have hone : ∀ p, (1 : Over.mk s ⟶ G').left p ∈ Set.range N.u := by
    obtain ⟨x₀, -, -, hx₀⟩ := hPt
    have e₁ : (1 : Over.mk s ⟶ G').left = s ≫ (1 : Over.mk (𝟙 S) ⟶ G').left := congrArg (fun f => f.left)
      (MonObj.comp_one (M := G') (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S))).symm
    intro p
    rw [e₁, ← hx₀]
    exact ⟨x₀ (s p), rfl⟩
  have hoU : IsOpen (Set.range N.u) := N.u.isOpenEmbedding.isOpen_range
  obtain ⟨σ₁, h₁, -⟩ := sec 1
  obtain ⟨σ₂, h₂, h₂'⟩ := sec g⁻¹
  have e₂ : σ₂ ≫ zT = 1 := by
    rw [MonObj.comp_mul, h₂, ← Category.assoc, h₂', Category.id_comp, mul_inv_cancel]
  have : IrreducibleSpace T := hT
  obtain ⟨t, ⟨p₀, hp₀⟩, ht⟩ := nonempty_preirreducible_inter (hoU.preimage (pullback.fst G'.hom s).continuous)
    (hoU.preimage zT.left.continuous)
    ⟨σ₁.left (IsLocalRing.closedPoint _), by
      have := hone (IsLocalRing.closedPoint _)
      rw [← h₁] at this
      exact this⟩
    ⟨σ₂.left (IsLocalRing.closedPoint _), by
      have := hone (IsLocalRing.closedPoint _)
      rw [← e₂] at this
      exact this⟩
  obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback sqk p₀ t hp₀
  let O : UΩ.Opens := ⟨(kO ≫ zT).left ⁻¹' Set.range N.u, hoU.preimage (kO ≫ zT).left.continuous⟩
  have hwO : w ∈ O := by
    show (kO ≫ zT).left w ∈ Set.range N.u
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    change zT.left (k w) ∈ Set.range N.u
    rw [hw]; exact ht
  have hirr : IrreducibleSpace UΩ := by
    refine (irreducibleSpace_def _).2 ⟨⟨w, trivial⟩, ?_⟩
    have := (IrreducibleSpace.isIrreducible_univ T).2.preimage k.isOpenEmbedding
    simpa using this
  obtain ⟨a, aΩ, ha, haf, has, hao⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hR.2.2.2 N.U N.smooth e he Ω xR hs hirr O ⟨w, hwO⟩
  let x : Over.mk (𝟙 S) ⟶ G' := Over.homMk
    (pullback.lift (π ≫ a) (𝟙 S) (by rw [Category.assoc, ha, Category.comp_id]; exact (Category.id_comp π).symm) ≫ N.u)
    (by rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
  refine ⟨a, x, ha, ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, ?_⟩
  let rO : Over.mk s ⟶ UO := Over.homMk aΩ (by
    change aΩ ≫ pullback.snd _ _ ≫ s = s
    rw [← Category.assoc, has, Category.id_comp])
  have hq : rO ≫ kO ≫ qT = 𝟙 _ := by
    ext
    change aΩ ≫ k ≫ pullback.snd _ _ = 𝟙 _
    rw [pullback.lift_snd, has]
  have hy : rO ≫ kO ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x := by
    ext
    change aΩ ≫ k ≫ pullback.fst _ _ = s ≫ pullback.lift (π ≫ a) (𝟙 S) _ ≫ N.u
    rw [pullback.lift_fst, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      show aΩ ≫ pullback.lift (pullback.fst N.U.hom xR) _ _ ≫ pullback.fst N.U.hom π = s ≫ π ≫ a
      rw [pullback.lift_fst, haf]
      simp only [xR, Category.assoc]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, has,
        Category.id_comp, Category.comp_id]
  have hz : g * ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x) = rO ≫ kO ≫ zT := by
    have hq' : (rO ≫ kO) ≫ qT = 𝟙 _ := by rw [Category.assoc]; exact hq
    have hy' : (rO ≫ kO) ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x := by
      rw [Category.assoc]; exact hy
    rw [← Category.assoc, MonObj.comp_mul, ← Category.assoc, hq', Category.id_comp, hy']
  rintro _ ⟨p, rfl⟩
  rw [hz]
  exact hao ⟨p, rfl⟩

end GlobalTheory.MoveNear
