import Mathlib
import Formalism.DoubleCosetMeasures.LatticeCoset
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FromBlocksMulInv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCompactSupportPhiU

noncomputable section

open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL

namespace GlobalTheory.SingleBlock

section Alg

variable {F : Type} [Field F]

/- English proof (translation)
Introduce `g h e`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Conclude with `congrArg (fun x : GL n F => (x : Matrix n n F) a b) e`.
-/
theorem map_subtype_injective (O : Subring F) (n : Type) [Fintype n] [DecidableEq n] :
    Function.Injective (GeneralLinearGroup.map (n := n) O.subtype) := by
  intro g h e
  apply Units.ext
  ext a b
  exact congrArg (fun x : GL n F => (x : Matrix n n F) a b) e

/- English proof (translation)
Introduce `g hg` and use `⟨GLRed.toO O r ⟨g, hP hg⟩, Units.ext rfl⟩`.
-/
theorem le_range_of_le_GLint {O : Subring F} {r : ℕ} {P : Subgroup (GL (Fin r) F)}
    (hP : P ≤ GLint O r) : P ≤ glInt O (Fin r) :=
  fun g hg => ⟨GLRed.toO O r ⟨g, hP hg⟩, Units.ext rfl⟩

/- English proof (translation)
Take `⟨g0, rfl⟩` from `hg`. Establish `: ((GeneralLinearGroup.det (GeneralLinearGroup.map (n` using `n) O.subtype g0) : Fˣ) : F) = O.subtype (g0 : Matrix n n O).det := by`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `Subtype.coe_prop _`.
-/
theorem det_mem_of_mem_glInt {O : Subring F} {n : Type} [Fintype n] [DecidableEq n] {g : GL n F}
    (hg : g ∈ glInt O n) : ((GeneralLinearGroup.det g : Fˣ) : F) ∈ O := by
  obtain ⟨g0, rfl⟩ := hg
  have : ((GeneralLinearGroup.det (GeneralLinearGroup.map (n := n) O.subtype g0) : Fˣ) : F) =
      O.subtype (g0 : Matrix n n O).det := by
    rw [RingHom.map_det]; rfl
  rw [this]; exact Subtype.coe_prop _

/- English proof (translation)
Rewrite using `[← map_inv]`. Conclude with `det_mem_of_mem_glInt (inv_mem hg)`.
-/
theorem det_inv_mem_of_mem_glInt {O : Subring F} {n : Type} [Fintype n] [DecidableEq n]
    {g : GL n F} (hg : g ∈ glInt O n) : (((GeneralLinearGroup.det g)⁻¹ : Fˣ) : F) ∈ O := by
  rw [← map_inv]; exact det_mem_of_mem_glInt (inv_mem hg)

/- English proof (translation)
Introduce `g`. Set `M : Matrix n n O` to `fun a b => Function.surjInv (IsLocalRing.residue_surjective (R := O)) ((g : Matrix n n _) a b)`. Establish `hM : M.map (IsLocalRing.residue O) = (g : Matrix n n _)`. Use extensionality with `a b`. Conclude with `Function.surjInv_eq _ _`.

Establish `hdet : IsUnit M.det`. Establish `h1 : IsUnit (IsLocalRing.residue O M.det)`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hM]`. Conclude with `(isUnit_iff_isUnit_det _).1 g.isUnit`. Conclude with `(isUnit_map_iff (IsLocalRing.residue O) _).1 h1`.

Conclude with `⟨GeneralLinearGroup.mk'' M hdet, Units.ext hM⟩`.
-/
theorem map_residue_surj (O : Type) [CommRing O] [IsLocalRing O] (n : Type) [Fintype n]
    [DecidableEq n] :
    Function.Surjective (GeneralLinearGroup.map (n := n) (IsLocalRing.residue O)) := by
  intro g
  let M : Matrix n n O := fun a b =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) ((g : Matrix n n _) a b)
  have hM : M.map (IsLocalRing.residue O) = (g : Matrix n n _) := by
    ext a b
    exact Function.surjInv_eq _ _
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (IsLocalRing.residue O M.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
      exact (isUnit_iff_isUnit_det _).1 g.isUnit
    exact (isUnit_map_iff (IsLocalRing.residue O) _).1 h1
  exact ⟨GeneralLinearGroup.mk'' M hdet, Units.ext hM⟩

/- English proof (translation)
Establish `h1 : ρ.ker.index ≠ 0` using `fun h => hK (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le (fun k hk => hρ k hk : K ≤ ρ.ker)))`. Establish `h2 : ρ (g ^ ρ.ker.index) = 1` using `ρ.ker.pow_index_mem g`. Establish `h3 : ‖((ρ g : ℂˣ) : ℂ)‖ ^ ρ.ker.index = 1`. Rewrite using `[← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h2]`. Simplify using the standard rewrite rules.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) h1).1 h3`.
-/
theorem norm_eq_one_of_finiteIndex {G : Type} [Group G] (K : Subgroup G) (hK : K.index ≠ 0)
    (ρ : G →* ℂˣ) (hρ : ∀ k ∈ K, ρ k = 1) (g : G) : ‖((ρ g : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : ρ.ker.index ≠ 0 := fun h => hK (Nat.eq_zero_of_zero_dvd
    (h ▸ Subgroup.index_dvd_of_le (fun k hk => hρ k hk : K ≤ ρ.ker)))
  have h2 : ρ (g ^ ρ.ker.index) = 1 := ρ.ker.pow_index_mem g
  have h3 : ‖((ρ g : ℂˣ) : ℂ)‖ ^ ρ.ker.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h2]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h1).1 h3

end Alg

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}

/- English proof (translation)
The claim follows from `Valuation.isOpen_integer`.
-/
theorem isOpen_integers : IsOpen ((𝒪[F] : Subring F) : Set F) :=
  Valuation.isOpen_integer

/- English proof (translation)
The claim follows from `IsNonarchimedeanLocalField.isCompact_closedBall F 1`.
-/
theorem isCompact_integers : IsCompact ((𝒪[F] : Subring F) : Set F) :=
  IsNonarchimedeanLocalField.isCompact_closedBall F 1

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace F`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := F)`. Use `infer_instance`.
-/
theorem t2Space_isNonarchimedeanLocalField_singleBlock : T2Space F := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

/- English proof (translation)
Introduce `h` and use `hϖ.ne_zero (Subtype.ext h)`.
-/
theorem unif_ne_zero (hϖ : Irreducible ϖ) : (ϖ : F) ≠ 0 :=
  fun h => hϖ.ne_zero (Subtype.ext h)

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Use `⟨c, c.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hc` as an intermediate fact.

Simplify `this.symm` using `[mul_comm]`. Introduce and unpack `⟨o, ho, e⟩`. Conclude with `⟨⟨o, ho⟩, Subtype.ext (by simpa [mul_comm] using e.symm)⟩`.
-/
theorem residue_eq_iff (hϖ : Irreducible ϖ) (x y : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x = IsLocalRing.residue 𝒪[F] y ↔
      ∃ o ∈ (𝒪[F] : Subring F), (x : F) - y = ϖ * o := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    have := congrArg Subtype.val hc
    simpa [mul_comm] using this.symm
  · rintro ⟨o, ho, e⟩
    exact ⟨⟨o, ho⟩, Subtype.ext (by simpa [mul_comm] using e.symm)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `hϖ.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext (mul_inv_cancel₀ (unif_ne_zero hϖ))))`. Introduce `x hx h`. Establish `h1 : IsUnit (⟨x, hx⟩ : 𝒪[F])`.

Assume the negation of the conclusion as `hn`. Establish `h2 : IsLocalRing.residue 𝒪[F] ⟨x, hx⟩ = IsLocalRing.residue 𝒪[F] 0`. Rewrite using `[map_zero, IsLocalRing.residue_eq_zero_iff]`. Conclude with `hn`. Take `⟨o, ho, e⟩` from `(residue_eq_iff hϖ _ _).1 h2`.

Conclude with `h o ho (by simpa using e)`. Take `⟨y, hy⟩` from `h1.exists_right_inv`. Establish `h3 : x * (y : F) = 1` using `congrArg Subtype.val hy`. Rewrite using `[← eq_inv_of_mul_eq_one_right h3]`. Conclude with `y.2`.
-/
theorem isLocalAt (hϖ : Irreducible ϖ) : IsLocalAt 𝒪[F] (ϖ : F) := by
  constructor
  · intro h
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h⟩
      (Subtype.ext (mul_inv_cancel₀ (unif_ne_zero hϖ))))
  · intro x hx h
    have h1 : IsUnit (⟨x, hx⟩ : 𝒪[F]) := by
      by_contra hn
      have h2 : IsLocalRing.residue 𝒪[F] ⟨x, hx⟩ = IsLocalRing.residue 𝒪[F] 0 := by
        rw [map_zero, IsLocalRing.residue_eq_zero_iff]; exact hn
      obtain ⟨o, ho, e⟩ := (residue_eq_iff hϖ _ _).1 h2
      exact h o ho (by simpa using e)
    obtain ⟨y, hy⟩ := h1.exists_right_inv
    have h3 : x * (y : F) = 1 := congrArg Subtype.val hy
    rw [← eq_inv_of_mul_eq_one_right h3]; exact y.2

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Nat.card (𝒪[F] ⧸ Ideal.span {ϖ}) = _`. Rewrite using `[← hϖ.maximalIdeal_eq]`. Both sides reduce to the same expression.
-/
theorem card_kF (hϖ : Irreducible ϖ) : Nat.card (kF 𝒪[F] (ϖ : F) ϖ.2) = Nat.card 𝓀[F] := by
  change Nat.card (𝒪[F] ⧸ Ideal.span {ϖ}) = _
  rw [← hϖ.maximalIdeal_eq]; rfl

/- English proof (translation)
The claim follows from `Nat.finite_of_card_ne_zero (by rw [card_kF hϖ]; exact Nat.card_pos.ne')`.
-/
theorem finite_kF (hϖ : Irreducible ϖ) : Finite (kF 𝒪[F] (ϖ : F) ϖ.2) :=
  Nat.finite_of_card_ne_zero (by rw [card_kF hϖ]; exact Nat.card_pos.ne')

/- English proof (translation)
Use extensionality with `g`. Establish `key : ∀ i j, IsLocalRing.residue 𝒪[F] ((g : Matrix (Fin r) (Fin r) 𝒪[F]) i j) = (1 : Matrix (Fin r) (Fin r) 𝓀[F]) i j ↔ (ϖ : F)⁻¹ * ((((g : Matrix (Fin r) (Fin r) 𝒪[F]) i j : 𝒪[F]) : F) - (1 : Matrix (Fin r) (Fin r) F) i j) ∈ 𝒪[F]`. Introduce `i j`. Establish `e : (1 : Matrix (Fin r) (Fin r) 𝓀[F]) i j = IsLocalRing.residue 𝒪[F] ((1 : Matrix (Fin r) (Fin r) 𝒪[F]) i j)`. Apply the tactic sequence `rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`.

Rewrite using `[e, residue_eq_iff hϖ, GLRed.one_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho, e⟩`. Rewrite using `[e, inv_mul_cancel_left₀ (unif_ne_zero hϖ)]` and apply the resulting hypothesis. Introduce `h`.

Conclude with `⟨_, h, by rw [mul_inv_cancel_left₀ (unif_ne_zero hϖ)]⟩`. Rewrite using `[Subgroup.mem_comap, MonoidHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Units.ext (Matrix.ext fun i j => (key i j).2 (h.2 i j))`.

Introduce `h`. Use `⟨⟨fun i j => ((g : Matrix (Fin r) (Fin r) 𝒪[F]) i j).2, fun i j => ?_⟩, fun i j => (key i j).1 ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `(((g⁻¹ : GL (Fin r) 𝒪[F]) : Matrix (Fin r) (Fin r) 𝒪[F]) i j).2`. Conclude with `congrArg (fun x : GL (Fin r) 𝓀[F] => (x : Matrix (Fin r) (Fin r) 𝓀[F]) i j) h`.
-/
theorem comap_congSub (hϖ : Irreducible ϖ) :
    (congSub 𝒪[F] (ϖ : F) r).comap (GeneralLinearGroup.map (n := Fin r) (𝒪[F]).subtype) =
      (GeneralLinearGroup.map (n := Fin r) (IsLocalRing.residue 𝒪[F])).ker := by
  ext g
  have key : ∀ i j, IsLocalRing.residue 𝒪[F] ((g : Matrix (Fin r) (Fin r) 𝒪[F]) i j) =
      (1 : Matrix (Fin r) (Fin r) 𝓀[F]) i j ↔
      (ϖ : F)⁻¹ * ((((g : Matrix (Fin r) (Fin r) 𝒪[F]) i j : 𝒪[F]) : F) -
        (1 : Matrix (Fin r) (Fin r) F) i j) ∈ 𝒪[F] := by
    intro i j
    have e : (1 : Matrix (Fin r) (Fin r) 𝓀[F]) i j =
        IsLocalRing.residue 𝒪[F] ((1 : Matrix (Fin r) (Fin r) 𝒪[F]) i j) := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [e, residue_eq_iff hϖ, GLRed.one_coe]
    constructor
    · rintro ⟨o, ho, e⟩
      rwa [e, inv_mul_cancel_left₀ (unif_ne_zero hϖ)]
    · intro h
      exact ⟨_, h, by rw [mul_inv_cancel_left₀ (unif_ne_zero hϖ)]⟩
  rw [Subgroup.mem_comap, MonoidHom.mem_ker]
  constructor
  · intro h
    exact Units.ext (Matrix.ext fun i j => (key i j).2 (h.2 i j))
  · intro h
    refine ⟨⟨fun i j => ((g : Matrix (Fin r) (Fin r) 𝒪[F]) i j).2, fun i j => ?_⟩,
      fun i j => (key i j).1 ?_⟩
    · rw [← map_inv]
      exact (((g⁻¹ : GL (Fin r) 𝒪[F]) : Matrix (Fin r) (Fin r) 𝒪[F]) i j).2
    · exact congrArg (fun x : GL (Fin r) 𝓀[F] => (x : Matrix (Fin r) (Fin r) 𝓀[F]) i j) h

/- English proof (translation)
Unfold `residueImage`. Rewrite using `[← Subgroup.relIndex_ker, ← comap_congSub hϖ, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self (le_range_of_le_GLint hP)]`.
-/
theorem relIndex_congSub (hϖ : Irreducible ϖ) {P : Subgroup (GL (Fin r) F)}
    (hP : P ≤ GLint 𝒪[F] r) :
    (congSub 𝒪[F] (ϖ : F) r).relIndex P = Nat.card (residueImage P) := by
  unfold residueImage
  rw [← Subgroup.relIndex_ker, ← comap_congSub hϖ, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self (le_range_of_le_GLint hP)]

/- English proof (translation)
Take `⟨g, rfl⟩` from `le_range_of_le_GLint le_rfl hk.1`. Establish `h1 : g ∈ (GeneralLinearGroup.map (n` using `Fin r) (IsLocalRing.residue 𝒪[F])).ker := by`. Rewrite using `[← comap_congSub hϖ]`. Conclude with `hk`. Establish `h2 : (IsLocalRing.residue 𝒪[F]).mapMatrix (g : Matrix (Fin r) (Fin r) 𝒪[F]) = 1` using `congrArg Units.val (MonoidHom.mem_ker.1 h1)`.

Use `hμ _ ((g : Matrix (Fin r) (Fin r) 𝒪[F]).det - 1) ?_ ?_` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, RingHom.map_det, h2, det_one, map_one, sub_self]`. Establish `: ((GeneralLinearGroup.det (GeneralLinearGroup.map (n` using `Fin r) (𝒪[F]).subtype g) : Fˣ) : F) = (𝒪[F]).subtype (g : Matrix (Fin r) (Fin r) 𝒪[F]).det := by`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem tame_det (hϖ : Irreducible ϖ) {μ : Fˣ →* ℂˣ} (hμ : IsTame μ) {k : GL (Fin r) F}
    (hk : k ∈ congSub 𝒪[F] (ϖ : F) r) : μ (GeneralLinearGroup.det k) = 1 := by
  obtain ⟨g, rfl⟩ := le_range_of_le_GLint le_rfl hk.1
  have h1 : g ∈ (GeneralLinearGroup.map (n := Fin r) (IsLocalRing.residue 𝒪[F])).ker := by
    rw [← comap_congSub hϖ]; exact hk
  have h2 : (IsLocalRing.residue 𝒪[F]).mapMatrix (g : Matrix (Fin r) (Fin r) 𝒪[F]) = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.1 h1)
  refine hμ _ ((g : Matrix (Fin r) (Fin r) 𝒪[F]).det - 1) ?_ ?_
  · rw [← IsLocalRing.residue_eq_zero_iff, map_sub, RingHom.map_det, h2, det_one, map_one, sub_self]
  · have : ((GeneralLinearGroup.det (GeneralLinearGroup.map (n := Fin r) (𝒪[F]).subtype g) : Fˣ) :
        F) = (𝒪[F]).subtype (g : Matrix (Fin r) (Fin r) 𝒪[F]).det := by
      rw [RingHom.map_det]; rfl
    rw [this]; simp

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Establish `h1` using `(hn.1 _).2 (det_mem_of_mem_glInt hg)`. Establish `h2` using `(hn.1 _).2 (det_inv_mem_of_mem_glInt hg)`. Rewrite `h2` using `[Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `le_antisymm h1 ((inv_le_one₀ (nrm.pos (Units.ne_zero _))).1 h2)`.
-/
theorem nrm_det {nrm : AbsoluteValue F ℝ} (hn : IsNormalisedAbs nrm) {n : Type} [Fintype n]
    [DecidableEq n] {g : GL n F} (hg : g ∈ glInt 𝒪[F] n) :
    nrm ((GeneralLinearGroup.det g : Fˣ) : F) = 1 := by
  have h1 := (hn.1 _).2 (det_mem_of_mem_glInt hg)
  have h2 := (hn.1 _).2 (det_inv_mem_of_mem_glInt hg)
  rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
  exact le_antisymm h1 ((inv_le_one₀ (nrm.pos (Units.ne_zero _))).1 h2)

/- English proof (translation)
Use extensionality with `h`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h0, rfl⟩, ⟨p, hp, e1⟩, e2⟩`. Take `⟨p0, rfl⟩` from `le_range_of_le_GLint hP hp`. Establish `hp0 : GeneralLinearGroup.map (n` using `Fin r) (IsLocalRing.residue 𝒪[F]) p0 ∈ residueImage P := Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.2 hp)`.

Use `Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.2 ((mem_blockPar_iff _ _).2 ⟨⟨_, hp0, ?_⟩, ?_⟩))` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `(residue_eq_iff hϖ _ _).2 (e1 i j)`. Use extensionality with `i j`. Use `(residue_eq_iff hϖ (h0.val (Sum.inr i) (Sum.inl j)) 0).2 (by rw [ZeroMemClass.coe_zero, sub_zero]; exact e2 i j)` as an intermediate fact.

Rewrite `this` using `[map_zero]`. Conclude with `this`. Introduce and unpack `⟨h0, hh, rfl⟩`. Take `⟨⟨pb, hpb, e1⟩, e2⟩` from `(mem_blockPar_iff _ _).1 (Subgroup.mem_comap.1 hh)`. Take `⟨p0, hp, rfl⟩` from `Subgroup.mem_map.1 hpb`.

Use `⟨⟨h0, rfl⟩, ⟨_, Subgroup.mem_comap.1 hp, fun i j => ?_⟩, fun i j => ?_⟩` and prove the remaining obligations. Conclude with `(residue_eq_iff hϖ _ _).1 (congrFun (congrFun e1 i) j)`. Use `(residue_eq_iff hϖ ((h0 : Matrix _ _ 𝒪[F]) (Sum.inr i) (Sum.inl j)) 0).1 (by rw [map_zero]; exact congrFun (congrFun e2 i) j)` as an intermediate fact. Rewrite `this` using `[ZeroMemClass.coe_zero, sub_zero]`. Conclude with `this`.
-/
theorem targetSet_eq (hϖ : Irreducible ϖ) {P : Subgroup (GL (Fin r) F)} (hP : P ≤ GLint 𝒪[F] r) :
    targetSet t 𝒪[F] (ϖ : F) P =
      (((blockPar t (residueImage P)).comap
        (GeneralLinearGroup.map (n := Fin r ⊕ Fin t) (IsLocalRing.residue 𝒪[F]))).map
        (GeneralLinearGroup.map (n := Fin r ⊕ Fin t) (𝒪[F]).subtype) :
          Subgroup (GL (Fin r ⊕ Fin t) F)) := by
  ext h
  constructor
  · rintro ⟨⟨h0, rfl⟩, ⟨p, hp, e1⟩, e2⟩
    obtain ⟨p0, rfl⟩ := le_range_of_le_GLint hP hp
    have hp0 : GeneralLinearGroup.map (n := Fin r) (IsLocalRing.residue 𝒪[F]) p0 ∈
        residueImage P := Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.2 hp)
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.2
      ((mem_blockPar_iff _ _).2 ⟨⟨_, hp0, ?_⟩, ?_⟩))
    · ext i j
      exact (residue_eq_iff hϖ _ _).2 (e1 i j)
    · ext i j
      have := (residue_eq_iff hϖ (h0.val (Sum.inr i) (Sum.inl j)) 0).2
        (by rw [ZeroMemClass.coe_zero, sub_zero]; exact e2 i j)
      rw [map_zero] at this
      exact this
  · rintro ⟨h0, hh, rfl⟩
    obtain ⟨⟨pb, hpb, e1⟩, e2⟩ := (mem_blockPar_iff _ _).1 (Subgroup.mem_comap.1 hh)
    obtain ⟨p0, hp, rfl⟩ := Subgroup.mem_map.1 hpb
    refine ⟨⟨h0, rfl⟩, ⟨_, Subgroup.mem_comap.1 hp, fun i j => ?_⟩, fun i j => ?_⟩
    · exact (residue_eq_iff hϖ _ _).1 (congrFun (congrFun e1 i) j)
    · have := (residue_eq_iff hϖ ((h0 : Matrix _ _ 𝒪[F]) (Sum.inr i) (Sum.inl j)) 0).1
        (by rw [map_zero]; exact congrFun (congrFun e2 i) j)
      rw [ZeroMemClass.coe_zero, sub_zero] at this
      exact this

/- English proof (translation)
Unfold `targetLevel`. Rewrite using `[targetSet_eq hϖ hP, Subgroup.closure_eq]`.
-/
theorem targetLevel_eq (hϖ : Irreducible ϖ) {P : Subgroup (GL (Fin r) F)}
    (hP : P ≤ GLint 𝒪[F] r) :
    targetLevel t 𝒪[F] (ϖ : F) P =
      ((blockPar t (residueImage P)).comap
        (GeneralLinearGroup.map (n := Fin r ⊕ Fin t) (IsLocalRing.residue 𝒪[F]))).map
        (GeneralLinearGroup.map (n := Fin r ⊕ Fin t) (𝒪[F]).subtype) := by
  unfold targetLevel
  rw [targetSet_eq hϖ hP, Subgroup.closure_eq]

/- English proof (translation)
Rewrite using `[targetLevel_eq hϖ hP, targetSet_eq hϖ hP]`.
-/
theorem coe_targetLevel (hϖ : Irreducible ϖ) {P : Subgroup (GL (Fin r) F)}
    (hP : P ≤ GLint 𝒪[F] r) :
    (targetLevel t 𝒪[F] (ϖ : F) P : Set (GL (Fin r ⊕ Fin t) F)) =
      targetSet t 𝒪[F] (ϖ : F) P := by
  rw [targetLevel_eq hϖ hP, targetSet_eq hϖ hP]

/- English proof (translation)
Unfold `glInt`. Rewrite using `[targetLevel_eq hϖ hP, MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ (map_subtype_injective _ _), Subgroup.relIndex_top_right, Subgroup.index_comap_of_surjective _ (map_residue_surj _ _)]`.
-/
theorem relIndex_targetLevel (hϖ : Irreducible ϖ) {P : Subgroup (GL (Fin r) F)}
    (hP : P ≤ GLint 𝒪[F] r) :
    (targetLevel t 𝒪[F] (ϖ : F) P).relIndex (glInt 𝒪[F] (Fin r ⊕ Fin t)) =
      (blockPar t (residueImage P)).index := by
  unfold glInt
  rw [targetLevel_eq hϖ hP, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ (map_subtype_injective _ _),
    Subgroup.relIndex_top_right, Subgroup.index_comap_of_surjective _ (map_residue_surj _ _)]

end Local

/- English proof (translation)
Introduce `F _ _ _ _ _ _ r t ϖ hϖ nrm hn μ η hμ hη _ P hKP hP lam hlam ν _ hν q Φ J normSq`. Establish `hO` using `isOpen_integers (F := F)`. Establish `hT : T2Space F` using `t2Space_isNonarchimedeanLocalField_singleBlock`. Establish `hϖ0` using `unif_ne_zero hϖ`. Establish `hloc` using `isLocalAt hϖ`.

Establish `hfin` using `finite_kF hϖ`. Establish `hq0 : q ≠ 0` using `Nat.card_pos.ne'`. Use `set ρ := blockChar μ P lam with hρdef`. Establish `hΦ : Φ = phiU 𝒪[F] (ϖ : F) P ρ` using `rfl`. Establish `hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub 𝒪[F] (ϖ : F) r), ρ ⟨k, hKP hk⟩ = 1`.

Introduce `k hk`. Rewrite using `[hρdef, blockChar_apply, hlam k hk, tame_det hϖ hμ hk]`. Simplify using the standard rewrite rules. Establish `hidx : ((congSub 𝒪[F] (ϖ : F) r).subgroupOf P).index = Nat.card (residueImage P)` using `relIndex_congSub hϖ hP`. Establish `hfinGL : Finite (GL (Fin r) 𝓀[F])`.

Establish `: Finite (Matrix (Fin r) (Fin r) 𝓀[F])` using `inferInstanceAs (Finite (Fin r → Fin r → 𝓀[F]))`. Conclude with `Finite.of_injective _ Units.val_injective`. Establish `hidx0 : ((congSub 𝒪[F] (ϖ : F) r).subgroupOf P).index ≠ 0`. Rewrite using `[hidx]`. Conclude with `Nat.card_pos.ne'`.

Establish `hρ1` using `norm_eq_one_of_finiteIndex _ hidx0 ρ fun k hk => hρ k hk`. Establish `hlam1` using `norm_eq_one_of_finiteIndex _ hidx0 lam fun k hk => hlam k hk`. Establish `hS : MeasurableSet (suppSet t 𝒪[F] (ϖ : F) P)` using `measurableSet_suppSet hO ϖ.2 hϖ0 hloc hKP hP`. Establish `hN : normSq = ((ν (suppSet t 𝒪[F] (ϖ : F) P)).toReal : ℂ)` using `weilPairing_self_eq_measure_support hS ρ hρ1 ν`. Establish `hqR : (q : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hq0`.

Establish `hvol : (ν (suppSet t 𝒪[F] (ϖ : F) P)).toReal = (Nat.card (residueImage P) : ℝ) * ((q : ℝ) ^ (r ^ 2))⁻¹ * ((q : ℝ) ^ (r * t))⁻¹`. Establish `h` using `measure_suppSet hO ϖ.2 hϖ0 hloc hKP hP ν`. Rewrite `h` using `[hν, mul_one, card_kF hϖ, ← Subgroup.index, hidx]`. Establish `h'` using `congrArg ENNReal.toReal h`. Simplify using `only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at h'`.

Rewrite using `[← h', pow_two, mul_comm r t]`. Express the relevant statement in the definitionally equal form `_ = _ * (q : ℝ) ^ _ * (q : ℝ) ^ _ * _ * _`. Clear the denominators using the available nonvanishing facts. Establish `hJ` using `coe_targetLevel (t := t) hϖ hP`. Establish `hi1 : ∀ g : GL (Fin r) F, g ∉ P → weilIP ν (weilPair μ η nrm g 1 Φ) Φ = 0`.

Introduce `g hg`. Rewrite using `[weilPair_one_right]`. Conclude with `suppJ F r t _ _ P ρ _ nrm ν g hg`. Establish `hi2 : ∀ g : P, weilIP ν (weilPair μ η nrm (g : GL (Fin r) F) 1 Φ) Φ = ((lam g : ℂˣ) : ℂ) * normSq`. Introduce `g`.

Establish `hg` using `le_range_of_le_GLint hP g.2`. Establish `e : ∀ x, weilPair μ η nrm (g : GL (Fin r) F) 1 Φ x = ((lam g : ℂˣ) : ℂ) * Φ x`. Introduce `x`. Unfold `weilPair`. Rewrite using `[nrm_det hn hg, hη _ (det_mem_of_mem_glInt hg) (det_inv_mem_of_mem_glInt hg), inv_one, Units.val_one, Matrix.one_mul, hΦ, phiU_mul_right hP ρ g, hρdef, blockChar_apply]`.

Simplify using `only [map_one, inv_one, mul_one, Units.val_one, Real.one_rpow, Complex.ofReal_one, Units.val_mul, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts. Express the relevant statement in the definitionally equal form `_ = _ * weilIP ν Φ Φ`. Unfold `weilIP`. Repeatedly rewrite using `[e, mul_assoc]`.

Rewrite using `[integral_const_mul]`. Establish `hv : (J.relIndex (glInt 𝒪[F] (Fin r ⊕ Fin t)) : ℂ) * normSq = ((∏ i ∈ Finset.Ioc t (r + t), (1 - ((q : ℝ) ^ i)⁻¹) : ℝ) : ℂ)`. Rewrite using `[hN, hvol, relIndex_targetLevel hϖ hP, ← index_blockPar (residueImage P)]`. Use `push_cast`. Both sides reduce to the same expression.

Use `⟨⟨isLocallyConstant_phiU hO ϖ.2 hϖ0 hloc hKP hP ρ hρ, hasCompactSupport_phiU isCompact_integers ϖ.2 hP ρ, hJ⟩, ⟨hi1, hi2⟩, ⟨?_, ?_⟩, ?_, ?_, hv, ?_⟩` and prove the remaining obligations. Introduce `ν₁ _ ν₂ _ h1 h2`. Establish `a1` using `volJadd F 𝒪[F] hO ϖ ϖ.2 hϖ0 hloc hfin r ν₁ P hKP hP`. Establish `a2` using `volII F 𝒪[F] hO ϖ ϖ.2 hϖ0 hfin t r ν₂`. Rewrite `a1` using `[h1, mul_one, card_kF hϖ, ← Subgroup.index, hidx]`.

Rewrite `a2` using `[h2, card_kF hϖ]`. Establish `b1` using `congrArg ENNReal.toReal a1`. Establish `b2` using `congrArg ENNReal.toReal a2`. Simplify using `only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_one] at b1 b2`. Rewrite using `[hN, hvol, ← b1, eq_inv_of_mul_eq_one_left b2, pow_two, mul_comm r t]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `_ * (q : ℝ) ^ _ * _ * _ = _ * ((q : ℝ) ^ _)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hN, hvol]`. Introduce `V _ _ σ _ x₁ x₂ hx dg _`.

Establish `hPo : IsOpen (P : Set (GL (Fin r) F))` using `Subgroup.isOpen_mono hKP (GLRed.congSub_open _ hO _ r)`. Establish `hPc : IsCompact (P : Set (GL (Fin r) F))` using `(GeneralLinearIntegersOpenCompact.glR_compact 𝒪[F] isCompact_integers r).of_isClosed_subset (P.isClosed_of_isOpen hPo) hP`. Establish `e : (fun g : GL (Fin r) F => weilIP ν (weilPair μ η nrm g 1 Φ) Φ * conj (inner ℂ x₂ (σ g x₁))) = (P : Set (GL (Fin r) F)).indicator (fun _ => normSq * conj (inner ℂ x₂ x₁))`. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ P`.

Rewrite using `[Set.indicator_of_mem (show g ∈ (P : Set _) from hg), hi2 ⟨g, hg⟩, hx ⟨g, hg⟩, inner_smul_right, map_mul]`. Establish `h1 : ((lam ⟨g, hg⟩ : ℂˣ) : ℂ) * conj ((lam ⟨g, hg⟩ : ℂˣ) : ℂ) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hlam1]`. Simplify using the standard rewrite rules. Take the linear combination `(normSq * conj (inner ℂ x₂ x₁)) * h1`.

Rewrite using `[Set.indicator_of_notMem (show g ∉ (P : Set _) from hg), hi1 g hg, zero_mul]`. Establish `hZ : localZ dg ν (μ * η) nrm Φ Φ (fun g => inner ℂ x₂ (σ g x₁)) = (((dg (P : Set (GL (Fin r) F))).toReal : ℝ) : ℂ) * normSq * conj (inner ℂ x₂ x₁)`. Unfold `localZ`. Repeatedly rewrite using `[← weilPair_one_right]`. Rewrite using `[e, integral_indicator_const _ hPo.measurableSet, Complex.real_smul, mul_assoc]`.

Both sides reduce to the same expression. Use `⟨?_, hZ, fun h1 => by rw [hZ, h1]; simp⟩` and prove the remaining obligations. Rewrite using `[e, integrable_indicator_iff hPo.measurableSet]`. Conclude with `integrableOn_const hPc.measure_lt_top.ne`. Establish `key : ∀ h ∈ J, ∃ k : P, ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₁₁ ∧ ∀ x ∈ suppSet t 𝒪[F] (ϖ : F) P, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x ∈ suppSet t 𝒪[F] (ϖ : F) P ∧ Φ ((h : Matrix (Fin r ⊕ Fin t) (Fi …`.

Introduce `h hh`. Take `⟨⟨h0, e0⟩, ⟨p, hp, e1⟩, e2⟩ : h ∈ targetSet t 𝒪[F] (ϖ : F) P` from `hJ ▸ hh`. Take `⟨k, hk, -⟩` from `exists_of_congr ϖ.2 hϖ0 hloc hKP hP ρ hρ ⟨p, hp⟩ e1`. Use `⟨k, hk, fun x hx => mul_left_mem ϖ.2 hϖ0 hloc hKP hP ρ hρ (fun i j => ?_) k hk e2 hx⟩` and prove the remaining obligations. Rewrite using `[← e0]`.

Conclude with `((h0 : Matrix _ _ 𝒪[F]) i j).2`. Introduce `h hh`. Take `⟨k, hk, hm⟩` from `key h hh`. Take `⟨k', -, hm'⟩` from `key h⁻¹ (J.inv_mem hh)`. Establish `hg : h ∈ glInt 𝒪[F] (Fin r ⊕ Fin t)` using `(show h ∈ targetSet t 𝒪[F] (ϖ : F) P from hJ ▸ hh).1`.

Use `⟨k, hk, funext fun x => ?_⟩` and prove the remaining obligations. Establish `e : Φ x = ((ρ k : ℂˣ) : ℂ) * Φ (((h⁻¹ : GL (Fin r ⊕ Fin t) F) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x)`. Distinguish the cases in `hx : ((h⁻¹ : GL (Fin r ⊕ Fin t) F) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x ∈ suppSet t 𝒪[F] (ϖ : F) P`. Rewrite using `[← (hm _ hx).2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Rewrite using `[hΦ, phiU_of_notMem ρ hx, mul_zero, phiU_of_notMem ρ fun h1 => hx (hm' x h1).1]`.

Unfold `weilPair`. Rewrite using `[nrm_det hn hg, Pi.smul_apply, e, Units.val_one, Matrix.mul_one]`. Simplify using `only [map_one, one_mul, mul_one, Units.val_one, Real.one_rpow, Complex.ofReal_one, Units.val_mul, Units.val_inv_eq_inv_val, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hv]`.

Use `congr 1`. Unfold `dFactor localZeta`. Rewrite using `[Finset.prod_inv_distrib, one_div, inv_inv]`.
-/
theorem localIntegralSingleBlock : LocalIntegralSingleBlock := by
  intro F _ _ _ _ _ _ r t ϖ hϖ nrm hn μ η hμ hη _ P hKP hP lam hlam ν _ hν q Φ J normSq
  have hO := isOpen_integers (F := F)
  have hT : T2Space F := t2Space_isNonarchimedeanLocalField_singleBlock
  have hϖ0 := unif_ne_zero hϖ
  have hloc := isLocalAt hϖ
  have hfin := finite_kF hϖ
  have hq0 : q ≠ 0 := Nat.card_pos.ne'
  set ρ := blockChar μ P lam with hρdef
  have hΦ : Φ = phiU 𝒪[F] (ϖ : F) P ρ := rfl
  have hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub 𝒪[F] (ϖ : F) r), ρ ⟨k, hKP hk⟩ = 1 := by
    intro k hk
    rw [hρdef, blockChar_apply, hlam k hk, tame_det hϖ hμ hk]; simp
  have hidx : ((congSub 𝒪[F] (ϖ : F) r).subgroupOf P).index = Nat.card (residueImage P) :=
    relIndex_congSub hϖ hP
  have hfinGL : Finite (GL (Fin r) 𝓀[F]) := by
    have : Finite (Matrix (Fin r) (Fin r) 𝓀[F]) :=
      inferInstanceAs (Finite (Fin r → Fin r → 𝓀[F]))
    exact Finite.of_injective _ Units.val_injective
  have hidx0 : ((congSub 𝒪[F] (ϖ : F) r).subgroupOf P).index ≠ 0 := by
    rw [hidx]; exact Nat.card_pos.ne'
  have hρ1 := norm_eq_one_of_finiteIndex _ hidx0 ρ fun k hk => hρ k hk
  have hlam1 := norm_eq_one_of_finiteIndex _ hidx0 lam fun k hk => hlam k hk
  have hS : MeasurableSet (suppSet t 𝒪[F] (ϖ : F) P) :=
    measurableSet_suppSet hO ϖ.2 hϖ0 hloc hKP hP
  have hN : normSq = ((ν (suppSet t 𝒪[F] (ϖ : F) P)).toReal : ℂ) := weilPairing_self_eq_measure_support hS ρ hρ1 ν
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have hvol : (ν (suppSet t 𝒪[F] (ϖ : F) P)).toReal =
      (Nat.card (residueImage P) : ℝ) * ((q : ℝ) ^ (r ^ 2))⁻¹ * ((q : ℝ) ^ (r * t))⁻¹ := by
    have h := measure_suppSet hO ϖ.2 hϖ0 hloc hKP hP ν
    rw [hν, mul_one, card_kF hϖ, ← Subgroup.index, hidx] at h
    have h' := congrArg ENNReal.toReal h
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at h'
    rw [← h', pow_two, mul_comm r t]
    change _ = _ * (q : ℝ) ^ _ * (q : ℝ) ^ _ * _ * _
    field_simp
  have hJ := coe_targetLevel (t := t) hϖ hP
  have hi1 : ∀ g : GL (Fin r) F, g ∉ P → weilIP ν (weilPair μ η nrm g 1 Φ) Φ = 0 := by
    intro g hg
    rw [weilPair_one_right]
    exact suppJ F r t _ _ P ρ _ nrm ν g hg
  have hi2 : ∀ g : P, weilIP ν (weilPair μ η nrm (g : GL (Fin r) F) 1 Φ) Φ =
      ((lam g : ℂˣ) : ℂ) * normSq := by
    intro g
    have hg := le_range_of_le_GLint hP g.2
    have e : ∀ x, weilPair μ η nrm (g : GL (Fin r) F) 1 Φ x = ((lam g : ℂˣ) : ℂ) * Φ x := by
      intro x
      unfold weilPair
      rw [nrm_det hn hg, hη _ (det_mem_of_mem_glInt hg) (det_inv_mem_of_mem_glInt hg), inv_one,
        Units.val_one, Matrix.one_mul, hΦ, phiU_mul_right hP ρ g, hρdef, blockChar_apply]
      simp only [map_one, inv_one, mul_one, Units.val_one, Real.one_rpow, Complex.ofReal_one,
        Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    change _ = _ * weilIP ν Φ Φ
    unfold weilIP
    simp_rw [e, mul_assoc]
    rw [integral_const_mul]
  have hv : (J.relIndex (glInt 𝒪[F] (Fin r ⊕ Fin t)) : ℂ) * normSq =
      ((∏ i ∈ Finset.Ioc t (r + t), (1 - ((q : ℝ) ^ i)⁻¹) : ℝ) : ℂ) := by
    rw [hN, hvol, relIndex_targetLevel hϖ hP, ← index_blockPar (residueImage P)]
    push_cast; rfl
  refine ⟨⟨isLocallyConstant_phiU hO ϖ.2 hϖ0 hloc hKP hP ρ hρ,
    hasCompactSupport_phiU isCompact_integers ϖ.2 hP ρ, hJ⟩, ⟨hi1, hi2⟩, ⟨?_, ?_⟩, ?_, ?_, hv, ?_⟩
  · intro ν₁ _ ν₂ _ h1 h2
    have a1 := volJadd F 𝒪[F] hO ϖ ϖ.2 hϖ0 hloc hfin r ν₁ P hKP hP
    have a2 := volII F 𝒪[F] hO ϖ ϖ.2 hϖ0 hfin t r ν₂
    rw [h1, mul_one, card_kF hϖ, ← Subgroup.index, hidx] at a1
    rw [h2, card_kF hϖ] at a2
    have b1 := congrArg ENNReal.toReal a1
    have b2 := congrArg ENNReal.toReal a2
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_one] at b1 b2
    rw [hN, hvol, ← b1, eq_inv_of_mul_eq_one_left b2, pow_two, mul_comm r t]
    congr 1
    change _ * (q : ℝ) ^ _ * _ * _ = _ * ((q : ℝ) ^ _)⁻¹
    field_simp
  · rw [hN, hvol]
  · intro V _ _ σ _ x₁ x₂ hx dg _
    have hPo : IsOpen (P : Set (GL (Fin r) F)) :=
      Subgroup.isOpen_mono hKP (GLRed.congSub_open _ hO _ r)
    have hPc : IsCompact (P : Set (GL (Fin r) F)) :=
      (GeneralLinearIntegersOpenCompact.glR_compact 𝒪[F] isCompact_integers r).of_isClosed_subset
        (P.isClosed_of_isOpen hPo) hP
    have e : (fun g : GL (Fin r) F =>
        weilIP ν (weilPair μ η nrm g 1 Φ) Φ * conj (inner ℂ x₂ (σ g x₁))) =
        (P : Set (GL (Fin r) F)).indicator (fun _ => normSq * conj (inner ℂ x₂ x₁)) := by
      funext g
      by_cases hg : g ∈ P
      · rw [Set.indicator_of_mem (show g ∈ (P : Set _) from hg), hi2 ⟨g, hg⟩, hx ⟨g, hg⟩,
          inner_smul_right, map_mul]
        have h1 : ((lam ⟨g, hg⟩ : ℂˣ) : ℂ) * conj ((lam ⟨g, hg⟩ : ℂˣ) : ℂ) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hlam1]; simp
        linear_combination (normSq * conj (inner ℂ x₂ x₁)) * h1
      · rw [Set.indicator_of_notMem (show g ∉ (P : Set _) from hg), hi1 g hg, zero_mul]
    have hZ : localZ dg ν (μ * η) nrm Φ Φ (fun g => inner ℂ x₂ (σ g x₁)) =
        (((dg (P : Set (GL (Fin r) F))).toReal : ℝ) : ℂ) * normSq * conj (inner ℂ x₂ x₁) := by
      unfold localZ
      simp_rw [← weilPair_one_right]
      rw [e, integral_indicator_const _ hPo.measurableSet, Complex.real_smul, mul_assoc]
      rfl
    refine ⟨?_, hZ, fun h1 => by rw [hZ, h1]; simp⟩
    rw [e, integrable_indicator_iff hPo.measurableSet]
    exact integrableOn_const hPc.measure_lt_top.ne
  · have key : ∀ h ∈ J, ∃ k : P, ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
        (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₁₁ ∧
        ∀ x ∈ suppSet t 𝒪[F] (ϖ : F) P,
          (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x ∈ suppSet t 𝒪[F] (ϖ : F) P ∧
          Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x) = ((ρ k : ℂˣ) : ℂ) * Φ x := by
      intro h hh
      obtain ⟨⟨h0, e0⟩, ⟨p, hp, e1⟩, e2⟩ : h ∈ targetSet t 𝒪[F] (ϖ : F) P := hJ ▸ hh
      obtain ⟨k, hk, -⟩ := exists_of_congr ϖ.2 hϖ0 hloc hKP hP ρ hρ ⟨p, hp⟩ e1
      refine ⟨k, hk, fun x hx => mul_left_mem ϖ.2 hϖ0 hloc hKP hP ρ hρ (fun i j => ?_) k hk e2 hx⟩
      rw [← e0]
      exact ((h0 : Matrix _ _ 𝒪[F]) i j).2
    intro h hh
    obtain ⟨k, hk, hm⟩ := key h hh
    obtain ⟨k', -, hm'⟩ := key h⁻¹ (J.inv_mem hh)
    have hg : h ∈ glInt 𝒪[F] (Fin r ⊕ Fin t) :=
      (show h ∈ targetSet t 𝒪[F] (ϖ : F) P from hJ ▸ hh).1
    refine ⟨k, hk, funext fun x => ?_⟩
    have e : Φ x = ((ρ k : ℂˣ) : ℂ) *
        Φ (((h⁻¹ : GL (Fin r ⊕ Fin t) F) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x) := by
      by_cases hx : ((h⁻¹ : GL (Fin r ⊕ Fin t) F) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x ∈
          suppSet t 𝒪[F] (ϖ : F) P
      · rw [← (hm _ hx).2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      · rw [hΦ, phiU_of_notMem ρ hx, mul_zero, phiU_of_notMem ρ fun h1 => hx (hm' x h1).1]
    unfold weilPair
    rw [nrm_det hn hg, Pi.smul_apply, e, Units.val_one, Matrix.mul_one]
    simp only [map_one, one_mul, mul_one, Units.val_one, Real.one_rpow, Complex.ofReal_one,
      Units.val_mul, Units.val_inv_eq_inv_val, smul_eq_mul]
    field_simp
  · rw [hv]
    congr 1
    unfold dFactor localZeta
    rw [Finset.prod_inv_distrib, one_div, inv_inv]

end GlobalTheory.SingleBlock
