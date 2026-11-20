import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single g r => simp [GDet.repAlg, diagRep]`.
-/
private theorem repAlg_comp {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G)
    (χ : Fin n → G →* Aˣ) (B : Type) [CommRing B] [Algebra A B] (y : MonoidAlgebra B H) :
    GDet.repAlg (diagRep fun i => (χ i).comp φ) B y =
      GDet.repAlg (diagRep χ) B (MonoidAlgebra.mapDomainRingHom B φ y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [GDet.repAlg, diagRep]

/- English proof (translation)
Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp [GFrame.star]`. Consider the case `add a b ha hb`. Simplify using `only [GFrame.star] at ha hb`. Simplify using `only [GFrame.star, map_add, MulOpposite.unop_add, ha, hb]`.

Consider the case `single g r`. Simplify using `[GFrame.star, GFrame.starOp, ← h.p₀_conj, h.eps_p₀]`.
-/
private theorem star_map {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (h : G.Hom G') (n : ℕ)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B : Type) [CommRing B] [Algebra O B] (y : MonoidAlgebra B G.G₀) :
    MonoidAlgebra.mapDomainRingHom B h.p₀ (G.frame.star O B n y) =
      G'.frame.star O B n (MonoidAlgebra.mapDomainRingHom B h.p₀ y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add a b ha hb =>
    simp only [GFrame.star] at ha hb
    simp only [GFrame.star, map_add, MulOpposite.unop_add, ha, hb]
  | single g r =>
    simp [GFrame.star, GFrame.starOp, ← h.p₀_conj, h.eps_p₀]

/- English proof (translation)
Introduce `l _ L G G' h n O _ _ _ r`. Use `⟨⟨fun i => (r.chib i).comp h.p₀, fun i => (r.chib_open i).preimage h.p₀_cont, ?_, ?_, r.psib, r.psib_open, r.th, r.th_comm⟩, fun _ => rfl, rfl, rfl⟩` and prove the remaining obligations. Introduce `i j hij`. Apply `r.chib_inj` to reduce the goal to its premises. Use extensionality with `g`.

Take `⟨g, rfl⟩` from `h.p₀_surj g`. Conclude with `congrArg Units.val (DFunLike.congr_fun hij g)`. Introduce `B _ _ _ _ y`. Use `r.polar B (MonoidAlgebra.mapDomainRingHom B h.p₀ y)` as an intermediate fact. Rewrite `this` using `[← star_map]`.

Express the relevant statement in the definitionally equal form `(GDet.repAlg _ B _).det = (GDet.repAlg _ B _).det`. Rewrite using `[repAlg_comp, repAlg_comp]`. Conclude with `this`.
-/
theorem UpperTheory.V.Pa.Core.resPull :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (h : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G'.frame O n), ∃ r' : Resid G.frame O n, Glob.Compat h r' r := by
  intro l _ L G G' h n O _ _ _ r
  refine ⟨⟨fun i => (r.chib i).comp h.p₀, fun i => (r.chib_open i).preimage h.p₀_cont, ?_, ?_,
    r.psib, r.psib_open, r.th, r.th_comm⟩, fun _ => rfl, rfl, rfl⟩
  · intro i j hij
    apply r.chib_inj
    ext g
    obtain ⟨g, rfl⟩ := h.p₀_surj g
    exact congrArg Units.val (DFunLike.congr_fun hij g)
  · intro B _ _ _ _ y
    have := r.polar B (MonoidAlgebra.mapDomainRingHom B h.p₀ y)
    rw [← star_map] at this
    change (GDet.repAlg _ B _).det = (GDet.repAlg _ B _).det
    rw [repAlg_comp, repAlg_comp]
    exact this
