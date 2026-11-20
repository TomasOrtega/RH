import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.ParHecke.Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

/- English proof (translation)
Use `⟨fun j hj => ?_, fun j hj => ⟨1, ⟨by simp, ?_⟩, fun y hy => by simpa using hy.1⟩⟩` and prove the remaining obligations. Rewrite `hj` using `[Finset.mem_singleton]`. Substitute `hj` using the available equality. Use `⟨one_mem _, ?_⟩` and prove the remaining obligations. Establish `: (1 : GL (A ⊕ D) k).1.toBlocks₂₂ = 1`.

Use extensionality with `i j`. Simplify using `[toBlocks₂₂, Matrix.one_apply]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[hg j]`.

Simplify using `using hj`.
-/
theorem isReps_central {g : GL (A ⊕ D) k} (hg : ∀ j, j * g = g * j) : IsReps g {1} (fun _ => 1) := by
  refine ⟨fun j hj => ?_, fun j hj => ⟨1, ⟨by simp, ?_⟩, fun y hy => by simpa using hy.1⟩⟩
  · rw [Finset.mem_singleton] at hj
    subst hj
    refine ⟨one_mem _, ?_⟩
    have : (1 : GL (A ⊕ D) k).1.toBlocks₂₂ = 1 := by
      ext i j; simp [toBlocks₂₂, Matrix.one_apply]
    rw [this]; simp
  · rw [hg j]; simpa using hj

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `using h _ _ (isReps_central hg)`. Introduce and unpack `rfl R d ⟨h1, h2⟩`. Take `⟨j₀, ⟨hj₀, -⟩, hu⟩` from `h2 1 (one_mem _)`.

Establish `hR : R = {j₀}`. Use `Finset.eq_singleton_iff_unique_mem.2 ⟨hj₀, fun j hj => hu j ⟨hj, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hg j]`. Use `inv_mem (h1 j hj).1` as an intermediate fact. Simplify using `using this`.

Substitute `hR` using the available equality. Rewrite using `[Finset.sum_singleton, hg j₀, map_mul, Module.End.mul_apply, hx j₀ (h1 j₀ hj₀).1 _ (h1 j₀ hj₀).2, map_smul, smul_smul]`. Simplify using the standard rewrite rules.
-/
theorem isTOp_central {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V)
    (ξ : kˣ →* ℂˣ) {g : GL (A ⊕ D) k} (hg : ∀ j, j * g = g * j) {x : V} (hx : x ∈ typeSpace π ξ) (y : V) :
    IsTOp π ξ g x y ↔ y = π g x := by
  constructor
  · intro h
    simpa using h _ _ (isReps_central hg)
  · rintro rfl R d ⟨h1, h2⟩
    obtain ⟨j₀, ⟨hj₀, -⟩, hu⟩ := h2 1 (one_mem _)
    have hR : R = {j₀} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨hj₀, fun j hj => hu j ⟨hj, ?_⟩⟩
      rw [hg j]
      have := inv_mem (h1 j hj).1
      simpa using this
    subst hR
    rw [Finset.sum_singleton, hg j₀, map_mul, Module.End.mul_apply, hx j₀ (h1 j₀ hj₀).1 _ (h1 j₀ hj₀).2,
      map_smul, smul_smul]
    simp

/- English proof (translation)
Use extensionality with `(a | a) (b | b)`. Conclude with `a.elim`. Conclude with `a.elim`. Conclude with `b.elim`. Simplify using `[Matrix.mul_apply, mul_comm]`.
-/
theorem comm_one (j g : GL (Empty ⊕ Unit) k) : j * g = g * j := by
  ext (a | a) (b | b)
  · exact a.elim
  · exact a.elim
  · exact b.elim
  · simp [Matrix.mul_apply, mul_comm]

/- English proof (translation)
Rewrite using `[← det_submatrix_equiv_self (Equiv.emptySum Empty Unit).symm]`. Simplify using `[Matrix.det_unique]`.
-/
theorem det_one_block (g : GL (Empty ⊕ Unit) k) : g.1.det = g.1 (.inr ()) (.inr ()) := by
  rw [← det_submatrix_equiv_self (Equiv.emptySum Empty Unit).symm]
  simp [Matrix.det_unique]

/- English proof (translation)
Introduce `g _ d hd` and use `by have : GeneralLinearGroup.det g = d := by ext rw [hd, GeneralLinearGroup.val_det_apply, det_one_block] simp [Matrix.det_unique, toBlocks₂₂] simp [detRep, this]`.
-/
theorem one_mem_type (χ : kˣ →* ℂˣ) : (1 : ℂ) ∈ typeSpace (detRep (Empty ⊕ Unit) χ) χ := fun g _ d hd => by
  have : GeneralLinearGroup.det g = d := by
    ext
    rw [hd, GeneralLinearGroup.val_det_apply, det_one_block]
    simp [Matrix.det_unique, toBlocks₂₂]
  simp [detRep, this]

/- English proof (translation)
Establish `hd : ∀ s : Finset Unit, GeneralLinearGroup.det (mtor (A` using `Empty) ϖ (indic s)) = ϖ ^ s.card := by`. Introduce `s`. Use `ext`. Rewrite using `[GeneralLinearGroup.val_det_apply, det_one_block, mtor, val_torusElt]`. Break down `Finset.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩` into its components or cases.

Simplify using `[indic]`. Establish `: s = {()}` using `Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun _ _ => rfl⟩`. Substitute `this` using the available equality. Simplify using `[indic]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, -, h⟩`. Use `(isTOp_central _ χ (fun j => comm_one j _) (one_mem_type χ) _).1 (h {()})` as an intermediate fact. Use `ext`. Simplify `this` using `[detRep, hd, genVal, Multiset.esymm, Multiset.powersetCard_one]`. Introduce and unpack `rfl`.

Use `⟨one_mem_type χ, by simp, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[isTOp_central _ χ (fun j => comm_one j _) (one_mem_type χ)]`. Break down `Finset.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩` into its components or cases. Simplify using `[detRep, hd, genVal, Multiset.esymm]`. Establish `: s = {()}` using `Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun _ _ => rfl⟩`.

Substitute `this` using the available equality. Simplify using `[detRep, hd, genVal, Multiset.esymm, Multiset.powersetCard_one]`.
-/
theorem isGen_rank_one (χ : kˣ →* ℂˣ) (ϖ : kˣ) (b : ℂˣ) :
    IsGen (detRep (Empty ⊕ Unit) χ) χ ϖ {b} (1 : ℂ) ↔ b = χ ϖ := by
  have hd : ∀ s : Finset Unit, GeneralLinearGroup.det (mtor (A := Empty) ϖ (indic s)) = ϖ ^ s.card := by
    intro s
    ext
    rw [GeneralLinearGroup.val_det_apply, det_one_block, mtor, val_torusElt]
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · simp [indic]
    · have : s = {()} := Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun _ _ => rfl⟩
      subst this
      simp [indic]
  constructor
  · rintro ⟨-, -, h⟩
    have := (isTOp_central _ χ (fun j => comm_one j _) (one_mem_type χ) _).1 (h {()})
    ext
    simpa [detRep, hd, genVal, Multiset.esymm, Multiset.powersetCard_one] using this
  · rintro rfl
    refine ⟨one_mem_type χ, by simp, fun s => ?_⟩
    rw [isTOp_central _ χ (fun j => comm_one j _) (one_mem_type χ)]
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · simp [detRep, hd, genVal, Multiset.esymm]
    · have : s = {()} := Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun _ _ => rfl⟩
      subst this
      simp [detRep, hd, genVal, Multiset.esymm, Multiset.powersetCard_one]

/- English proof (translation)
Introduce `j hj d hd v`. Use `one_mem_type χ j hj d hd` as an intermediate fact. Establish `h2 : detRep (Empty ⊕ Unit) χ j v = v • detRep (Empty ⊕ Unit) χ j 1`. Rewrite using `[← map_smul]`. Simplify using the standard rewrite rules.

Rewrite using `[LinearMap.id_apply, h2, this]`. Simplify using `[mul_comm]`.
-/
theorem isCoType_rank_one (χ : kˣ →* ℂˣ) : IsCoType (detRep (Empty ⊕ Unit) χ) χ LinearMap.id := by
  intro j hj d hd v
  have := one_mem_type χ j hj d hd
  have h2 : detRep (Empty ⊕ Unit) χ j v = v • detRep (Empty ⊕ Unit) χ j 1 := by
    rw [← map_smul]; simp
  rw [LinearMap.id_apply, h2, this]
  simp [mul_comm]

/- English proof (translation)
Simplify using `[omTwo]`.
-/
theorem omTwo_self {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (u : Matrix b a k → ℂ) : omTwo μ μ g h u = om μ⁻¹ g h u := by
  simp [omTwo]

/- English proof (translation)
Simplify using `[omTwo, om]`. Clear the denominators using the available nonvanishing facts.
-/
theorem omTwo_apply {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μS μT : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (u : Matrix b a k → ℂ) (x : Matrix b a k) :
    omTwo μS μT g h u x = (((μT (GeneralLinearGroup.det g))⁻¹ * μS (GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      om 1 g h u x := by
  simp [omTwo, om]
  field_simp

/- English proof (translation)
Establish `h : InSupp (fromBlocks 1 0 0 y : Matrix (A ⊕ D) (A ⊕ D') k)`. Use `⟨?_, by simp, fun i j => by simp⟩` and prove the remaining obligations. Introduce and unpack `(i | i) (j | j)`. Conclude with `one_int i j`. Conclude with `zero_mem _`.

Conclude with `zero_mem _`. Conclude with `hy i j`. Establish `: Units.mk0 _ h.det_ne = 1` using `by ext; simp`. Simplify using `[liftS, schur, datum, dif_pos h, this]`.
-/
theorem liftS_diag (ξ : kˣ →* ℂˣ) (ψ : Matrix D D' k → ℂ) (y : Matrix D D' k) (hy : ∀ i j, y i j ∈ 𝒪[k]) :
    liftS ξ ψ (fromBlocks (1 : Matrix A A k) 0 0 y) = ψ y := by
  have h : InSupp (fromBlocks 1 0 0 y : Matrix (A ⊕ D) (A ⊕ D') k) := by
    refine ⟨?_, by simp, fun i j => by simp⟩
    rintro (i | i) (j | j)
    · exact one_int i j
    · exact zero_mem _
    · exact zero_mem _
    · exact hy i j
  have : Units.mk0 _ h.det_ne = 1 := by ext; simp
  simp [liftS, schur, datum, dif_pos h, this]

/- English proof (translation)
Establish `: absPow k 0 ϖ = 1` using `by ext; simp [val_absPow]`. Simplify using `[segL, this]`.
-/
theorem segL_one (ϖ : kˣ) (z : ℂˣ) : segL ϖ z 1 = {z} := by
  have : absPow k 0 ϖ = 1 := by ext; simp [val_absPow]
  simp [segL, this]

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology ho`. Set `f : G → G ⧸ J` to `fun j => QuotientGroup.mk (j * g)`. Establish `hf : Continuous f` using `QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)`. Establish `hfin : (f '' J).Finite` using `(hc.image hf).finite_of_discrete`. Establish `hex : ∀ c ∈ f '' J, ∃ j ∈ J, f j = c` using `fun c hc => hc`.

Use `choose! s hs hs' using hex`. Use `⟨hfin.toFinset.image s, ?_, fun j hj => ⟨s (f j), ⟨?_, ?_⟩, ?_⟩⟩` and prove the remaining obligations. Introduce `j hj`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hj`. Conclude with `hs c (hfin.mem_toFinset.1 hc)`.

Conclude with `Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨j, hj, rfl⟩)`. Conclude with `QuotientGroup.eq.1 (hs' (f j) ⟨j, hj, rfl⟩)`. Introduce and unpack `y ⟨hy, hy'⟩`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hy`. Establish `: f (s c) = f j` using `QuotientGroup.eq.2 hy'`.

Rewrite using `[← this, hs' c (hfin.mem_toFinset.1 hc)]`.
-/
theorem exists_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G)
    (ho : IsOpen (J : Set G)) (hc : IsCompact (J : Set G)) (g : G) :
    ∃ R : Finset G, (∀ j ∈ R, j ∈ J) ∧ ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J := by
  classical
  haveI : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology ho
  let f : G → G ⧸ J := fun j => QuotientGroup.mk (j * g)
  have hf : Continuous f := QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  have hfin : (f '' J).Finite := (hc.image hf).finite_of_discrete
  have hex : ∀ c ∈ f '' J, ∃ j ∈ J, f j = c := fun c hc => hc
  choose! s hs hs' using hex
  refine ⟨hfin.toFinset.image s, ?_, fun j hj => ⟨s (f j), ⟨?_, ?_⟩, ?_⟩⟩
  · intro j hj
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hj
    exact hs c (hfin.mem_toFinset.1 hc)
  · exact Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨j, hj, rfl⟩)
  · exact QuotientGroup.eq.1 (hs' (f j) ⟨j, hj, rfl⟩)
  · rintro y ⟨hy, hy'⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hy
    have : f (s c) = f j := QuotientGroup.eq.2 hy'
    rw [← this, hs' c (hfin.mem_toFinset.1 hc)]

/- English proof (translation)
Establish `: (parahoric k A D : Set (GL (A ⊕ D) k)) = (KO k (A ⊕ D) : Set _) ∩ ⋂ i, ⋂ j, (fun g : GL (A ⊕ D) k => g.1 (.inr i) (.inl j)) ⁻¹' {x : k | valuation k x < 1}`. Use extensionality with `g`. Simplify using `[mem_parahoric]`. Rewrite using `[this]`. Use `SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)` and prove the remaining obligations.

Use `IsOpen.preimage (Units.continuous_val.matrix_elem _ _) ?_` and prove the remaining obligations. Simplify `(valuation k).isOpen_ball 1` using `[Valuation.restrict_lt_one_iff]`.
-/
theorem isOpen_parahoric : IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  have : (parahoric k A D : Set (GL (A ⊕ D) k)) = (KO k (A ⊕ D) : Set _) ∩
      ⋂ i, ⋂ j, (fun g : GL (A ⊕ D) k => g.1 (.inr i) (.inl j)) ⁻¹' {x : k | valuation k x < 1} := by
    ext g; simp [mem_parahoric]
  rw [this]
  refine SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  refine IsOpen.preimage (Units.continuous_val.matrix_elem _ _) ?_
  simpa [Valuation.restrict_lt_one_iff] using (valuation k).isOpen_ball 1

/- English proof (translation)
The claim follows from `SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_parahoric) fun _ h => (mem_parahoric.1 h).1`.
-/
theorem isCompact_parahoric : IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_parahoric)
    fun _ h => (mem_parahoric.1 h).1

/- English proof (translation)
Take `⟨h, hh, rfl⟩` from `hj`. Introduce `h0`. Establish `e1 : (GeneralLinearGroup.map (n` using `A ⊕ D) (algebraMap 𝒪[k] k) h).1.toBlocks₂₂ = (algebraMap 𝒪[k] k).mapMatrix h.1.toBlocks₂₂ := rfl`. Rewrite `h0` using `[e1, ← RingHom.map_det]`. Establish `h1 : h.1.toBlocks₂₂.det = 0` using `Subtype.ext h0`.

Use `set u := GeneralLinearGroup.map (n := A ⊕ D) (IsLocalRing.residue 𝒪[k]) h with hu`. Establish `h21 : u.1.toBlocks₂₁ = 0`. Use extensionality with `i j`. Conclude with `hh (i := .inr i) (j := .inl j) (show false < true by decide)`. Establish `h22 : u.1.toBlocks₂₂.det = 0`.

Establish `: u.1.toBlocks₂₂ = (IsLocalRing.residue 𝒪[k]).mapMatrix h.1.toBlocks₂₂` using `rfl`. Rewrite using `[this, ← RingHom.map_det, h1, map_zero]`. Use `u.det_ne_zero` as an intermediate fact. Rewrite `this` using `[← fromBlocks_toBlocks u.1, h21, det_fromBlocks_zero₂₁, h22, mul_zero]`. Conclude with `this rfl`.
-/
theorem det_lower_ne {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) : j.1.toBlocks₂₂.det ≠ 0 := by
  obtain ⟨h, hh, rfl⟩ := hj
  intro h0
  have e1 : (GeneralLinearGroup.map (n := A ⊕ D) (algebraMap 𝒪[k] k) h).1.toBlocks₂₂ =
      (algebraMap 𝒪[k] k).mapMatrix h.1.toBlocks₂₂ := rfl
  rw [e1, ← RingHom.map_det] at h0
  have h1 : h.1.toBlocks₂₂.det = 0 := Subtype.ext h0
  set u := GeneralLinearGroup.map (n := A ⊕ D) (IsLocalRing.residue 𝒪[k]) h with hu
  have h21 : u.1.toBlocks₂₁ = 0 := by
    ext i j
    exact hh (i := .inr i) (j := .inl j) (show false < true by decide)
  have h22 : u.1.toBlocks₂₂.det = 0 := by
    have : u.1.toBlocks₂₂ = (IsLocalRing.residue 𝒪[k]).mapMatrix h.1.toBlocks₂₂ := rfl
    rw [this, ← RingHom.map_det, h1, map_zero]
  have := u.det_ne_zero
  rw [← fromBlocks_toBlocks u.1, h21, det_fromBlocks_zero₂₁, h22, mul_zero] at this
  exact this rfl

/- English proof (translation)
Take `⟨R, h1, h2⟩` from `exists_reps _ isOpen_parahoric isCompact_parahoric g`. Use `⟨R, fun j => if h : j.1.toBlocks₂₂.det ≠ 0 then Units.mk0 _ h else 1, fun j hj => ⟨h1 j hj, ?_⟩, h2⟩` and prove the remaining obligations. Simplify using `[det_lower_ne (h1 j hj)]`.
-/
theorem exists_isReps (g : GL (A ⊕ D) k) : ∃ R d, IsReps g R d := by
  classical
  obtain ⟨R, h1, h2⟩ := exists_reps _ isOpen_parahoric isCompact_parahoric g
  refine ⟨R, fun j => if h : j.1.toBlocks₂₂.det ≠ 0 then Units.mk0 _ h else 1, fun j hj => ⟨h1 j hj, ?_⟩, h2⟩
  simp [det_lower_ne (h1 j hj)]

/- English proof (translation)
Take `⟨R, d, hR⟩` from `exists_isReps g`. Rewrite using `[h R d hR, h' R d hR]`.
-/
theorem isTOp_unique {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V)
    (ξ : kˣ →* ℂˣ) (g : GL (A ⊕ D) k) {x y y' : V} (h : IsTOp π ξ g x y) (h' : IsTOp π ξ g x y') : y = y' := by
  obtain ⟨R, d, hR⟩ := exists_isReps g
  rw [h R d hR, h' R d hR]

/- English proof (translation)
Take `⟨R, h1, h2⟩` from `exists_reps (KO k D) SplitFlip.isOpen_KO SplitFlip.isCompact_KO g`. Use `⟨R.image (· * g), ?_, fun κ hκ => ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨j, hj, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `⟨j, h1 j hj, 1, one_mem _, by simp⟩`.

Take `⟨j, ⟨hj, hj'⟩, hu⟩` from `h2 κ hκ`. Use `⟨j * g, ⟨Finset.mem_image_of_mem _ hj, hj'⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨hy, hy'⟩`. Take `⟨j2, hj2, rfl⟩` from `Finset.mem_image.1 hy`. Rewrite using `[hu j2 ⟨hj2, hy'⟩]`.
-/
theorem exists_isRepsK (g : GL D k) : ∃ R, IsRepsK g R := by
  classical
  obtain ⟨R, h1, h2⟩ := exists_reps (KO k D) SplitFlip.isOpen_KO SplitFlip.isCompact_KO g
  refine ⟨R.image (· * g), ?_, fun κ hκ => ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨j, h1 j hj, 1, one_mem _, by simp⟩
  · obtain ⟨j, ⟨hj, hj'⟩, hu⟩ := h2 κ hκ
    refine ⟨j * g, ⟨Finset.mem_image_of_mem _ hj, hj'⟩, ?_⟩
    rintro y ⟨hy, hy'⟩
    obtain ⟨j2, hj2, rfl⟩ := Finset.mem_image.1 hy
    rw [hu j2 ⟨hj2, hy'⟩]

/- English proof (translation)
Use `⟨fun g => (sphSection k n (1 - (Fintype.card n : ℂ) / 2) (io k n (g, 1))).re, fun κ hκ g => ⟨?_, ?_⟩, fun e => ?_⟩` and prove the remaining obligations. Use `sphSection_io_biinv (1 - (Fintype.card n : ℂ) / 2) g hκ (one_mem _)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Simplify using `only [this]`. Use `sphSection_io_biinv (1 - (Fintype.card n : ℂ) / 2) g (one_mem _) hκ` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Simplify using `only [this]`. Simplify using `only [sphSection_torusElt hϖ]`. Establish `: -((Fintype.card n : ℂ) / 2 + (1 - (Fintype.card n : ℂ) / 2)) * ((∑ i, |e i| : ℤ) : ℂ) = ((-(sumAbs e) : ℤ) : ℂ)`. Simplify using `[sumAbs]`.

Rewrite using `[this, Complex.cpow_intCast, ← Complex.ofReal_natCast, ← Complex.ofReal_zpow, Complex.ofReal_re]`.
-/
theorem exists_isHgt {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ∃ H : GL n k → ℝ, IsHgt ϖ H := by
  refine ⟨fun g => (sphSection k n (1 - (Fintype.card n : ℂ) / 2) (io k n (g, 1))).re, fun κ hκ g => ⟨?_, ?_⟩, fun e => ?_⟩
  · have := sphSection_io_biinv (1 - (Fintype.card n : ℂ) / 2) g hκ (one_mem _)
    rw [mul_one] at this
    simp only [this]
  · have := sphSection_io_biinv (1 - (Fintype.card n : ℂ) / 2) g (one_mem _) hκ
    rw [one_mul] at this
    simp only [this]
  · simp only [sphSection_torusElt hϖ]
    have : -((Fintype.card n : ℂ) / 2 + (1 - (Fintype.card n : ℂ) / 2)) * ((∑ i, |e i| : ℤ) : ℂ) =
        ((-(sumAbs e) : ℤ) : ℂ) := by
      simp [sumAbs]
    rw [this, Complex.cpow_intCast, ← Complex.ofReal_natCast, ← Complex.ofReal_zpow, Complex.ofReal_re]

end GlobalTheory.ParHecke.Model

end
