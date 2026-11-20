import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc Matrix

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.GL

section Mat

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]

variable (O) in
def Ent (g : GL (Fin 2) K) : Prop := ∀ s t, (g : Matrix (Fin 2) (Fin 2) K) s t ∈ Set.range (algebraMap O K)

abbrev sc (s : Kˣ) : GL (Fin 2) K := GeneralLinearGroup.scalar (Fin 2) s

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [sc, GeneralLinearGroup.scalar, h]`.
-/
theorem sc_val (s : Kˣ) : ((sc s : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (s : K) • 1 := by
  ext i j
  by_cases h : i = j <;> simp [sc, GeneralLinearGroup.scalar, h]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, sc_val, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`.
-/
theorem sc_comm (s : Kˣ) (g : GL (Fin 2) K) : sc s * g = g * sc s := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sc_val, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/- English proof (translation)
Take `⟨a, rfl⟩` from `h`. Conclude with `fun s t => ⟨(a : Matrix (Fin 2) (Fin 2) O) s t, rfl⟩`.
-/
theorem kg_ent {g : GL (Fin 2) K} (h : g ∈ KG O K) : Ent O g := by
  obtain ⟨a, rfl⟩ := h
  exact fun s t => ⟨(a : Matrix (Fin 2) (Fin 2) O) s t, rfl⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `h`. Use `⟨GeneralLinearGroup.det a, ?_⟩` and prove the remaining obligations. Simplify using `[RingHom.map_det]`.
-/
theorem kg_det {g : GL (Fin 2) K} (h : g ∈ KG O K) :
    ∃ u : Oˣ, (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K u := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨GeneralLinearGroup.det a, ?_⟩
  simp [RingHom.map_det]

/- English proof (translation)
Use `choose a ha using h`. Establish `hg : (g : Matrix (Fin 2) (Fin 2) K) = (algebraMap O K).mapMatrix (Matrix.of a)`. Use extensionality with `s t`. Simplify using `[ha]`. Establish `hd : (Matrix.of a).det = u`.

Apply `IsFractionRing.injective O K` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, ← hg, hu]`. Use `⟨GeneralLinearGroup.mk'' (Matrix.of a) (hd ▸ u.isUnit), Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Both sides reduce to the same expression.
-/
theorem kg_of_det [IsFractionRing O K] {g : GL (Fin 2) K} (h : Ent O g) (u : Oˣ)
    (hu : (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K u) : g ∈ KG O K := by
  choose a ha using h
  have hg : (g : Matrix (Fin 2) (Fin 2) K) = (algebraMap O K).mapMatrix (Matrix.of a) := by
    ext s t
    simp [ha]
  have hd : (Matrix.of a).det = u := by
    apply IsFractionRing.injective O K
    rw [RingHom.map_det, ← hg, hu]
  refine ⟨GeneralLinearGroup.mk'' (Matrix.of a) (hd ▸ u.isUnit), Units.ext ?_⟩
  rw [hg]
  rfl

/- English proof (translation)
Use `choose a ha using h`. Conclude with `⟨a 0 0 * a 1 1 - a 0 1 * a 1 0, by simp [det_fin_two, ha]⟩`.
-/
theorem ent_det {g : GL (Fin 2) K} (h : Ent O g) : ∃ r : O, (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K r := by
  choose a ha using h
  exact ⟨a 0 0 * a 1 1 - a 0 1 * a 1 0, by simp [det_fin_two, ha]⟩

/- English proof (translation)
Take `⟨r, hr⟩` from `ent_det h`. Take `⟨r', hr'⟩` from `ent_det h'`. Establish `: r * r' = 1`. Apply `IsFractionRing.injective O K` to reduce the goal to its premises. Rewrite using `[map_mul, ← hr, ← hr', ← det_mul, ← Units.val_mul, mul_inv_cancel, map_one]`.

Simplify using the standard rewrite rules. Conclude with `kg_of_det h (Units.mkOfMulEqOne r r' this) hr`.
-/
theorem kg_of_inv [IsFractionRing O K] {g : GL (Fin 2) K} (h : Ent O g) (h' : Ent O g⁻¹) : g ∈ KG O K := by
  obtain ⟨r, hr⟩ := ent_det h
  obtain ⟨r', hr'⟩ := ent_det h'
  have : r * r' = 1 := by
    apply IsFractionRing.injective O K
    rw [map_mul, ← hr, ← hr', ← det_mul, ← Units.val_mul, mul_inv_cancel, map_one]
    simp
  exact kg_of_det h (Units.mkOfMulEqOne r r' this) hr

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h haveI : (GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range.Normal := ⟨by`. Introduce and unpack `_ ⟨s, rfl⟩ g`. Conclude with `⟨s, by rw [← sc_comm s g, mul_inv_cancel_right]⟩⟩`. Establish `h' : g ∈ ((ZK O K : Subgroup _) : Set (GL (Fin 2) K))` using `h`.

Rewrite `h'` using `[ZK, Subgroup.normal_mul]`. Take `⟨_, ⟨s, rfl⟩, k, hk, rfl⟩` from `h'`. Conclude with `⟨s, k, hk, rfl⟩`. Introduce and unpack `⟨s, k, hk, rfl⟩`. Conclude with `Subgroup.mul_mem_sup ⟨s, rfl⟩ hk`.
-/
theorem zk_iff {g : GL (Fin 2) K} : g ∈ ZK O K ↔ ∃ s : Kˣ, ∃ k ∈ KG O K, g = sc s * k := by
  constructor
  · intro h
    haveI : (GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range.Normal := ⟨by
      rintro _ ⟨s, rfl⟩ g
      exact ⟨s, by rw [← sc_comm s g, mul_inv_cancel_right]⟩⟩
    have h' : g ∈ ((ZK O K : Subgroup _) : Set (GL (Fin 2) K)) := h
    rw [ZK, Subgroup.normal_mul] at h'
    obtain ⟨_, ⟨s, rfl⟩, k, hk, rfl⟩ := h'
    exact ⟨s, k, hk, rfl⟩
  · rintro ⟨s, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup ⟨s, rfl⟩ hk

/- English proof (translation)
Take `⟨w, k, hk, rfl⟩` from `zk_iff.1 h`. Take `⟨v, hv⟩` from `kg_det hk`. Establish `hw : ∃ r : O, algebraMap O K r = w`. Break down `ValuationRing.isInteger_or_isInteger O (w : K) with h | ⟨r, hr⟩` into its components or cases. Conclude with `h`.

Rewrite `hu` using `[Units.val_mul, sc_val, det_mul, det_smul, hv]`. Establish `: r * (r * u) = v`. Apply `IsFractionRing.injective O K` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, hr, ← hu]`. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Establish `hr' : IsUnit r` using `isUnit_of_mul_isUnit_left (this ▸ v.isUnit)`. Take `⟨r', hr''⟩` from `hr'.exists_right_inv`. Use `⟨r', ?_⟩` and prove the remaining obligations. Use `congrArg (algebraMap O K) hr''` as an intermediate fact.

Rewrite `this` using `[map_mul, hr, map_one]`. Clear denominators, using `at this` for the nonvanishing conditions. Conclude with `this`. Take `⟨r, hr⟩` from `hw`. Introduce `s t`.

Take `⟨a, ha⟩` from `kg_ent hk s t`. Conclude with `⟨r * a, by simp [sc_val, hr, ha]⟩`.
-/
theorem ent_of_zk [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] {g : GL (Fin 2) K} (u : Oˣ)
    (hu : (g : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K u) (h : g ∈ ZK O K) : Ent O g := by
  obtain ⟨w, k, hk, rfl⟩ := zk_iff.1 h
  obtain ⟨v, hv⟩ := kg_det hk
  have hw : ∃ r : O, algebraMap O K r = w := by
    rcases ValuationRing.isInteger_or_isInteger O (w : K) with h | ⟨r, hr⟩
    · exact h
    · rw [Units.val_mul, sc_val, det_mul, det_smul, hv] at hu
      have : r * (r * u) = v := by
        apply IsFractionRing.injective O K
        rw [map_mul, map_mul, hr, ← hu]
        simp
        field_simp
      have hr' : IsUnit r := isUnit_of_mul_isUnit_left (this ▸ v.isUnit)
      obtain ⟨r', hr''⟩ := hr'.exists_right_inv
      refine ⟨r', ?_⟩
      have := congrArg (algebraMap O K) hr''
      rw [map_mul, hr, map_one] at this
      field_simp at this
      exact this
  obtain ⟨r, hr⟩ := hw
  intro s t
  obtain ⟨a, ha⟩ := kg_ent hk s t
  exact ⟨r * a, by simp [sc_val, hr, ha]⟩

end Mat

section LL

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {τ : K}

variable (τ) in
abbrev b0 : Module.Basis (Fin 2) K (Etau K τ) := QuadraticAlgebra.basis (-1) τ

variable (τ) in
abbrev j0 : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix (b0 τ)

/- English proof (translation)
Simplify using `[Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis]`.
-/
theorem leftMulMatrixEmbedding_omega_trace : (j0 τ ω).trace = τ := by
  simp [Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis]

/- English proof (translation)
Simplify using `[Matrix.det_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis, QuadraticAlgebra.norm_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leftMulMatrixEmbedding_det_eq_norm (x : Etau K τ) : (j0 τ x).det = QuadraticAlgebra.norm x := by
  simp [Matrix.det_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis, QuadraticAlgebra.norm_def]
  ring

variable (τ) in
def su (s : Kˣ) : (Etau K τ)ˣ := Units.map (algebraMap K (Etau K τ) : K →* Etau K τ) s

/- English proof (translation)
Simplify using `[su, Algebra.smul_def]`.
-/
theorem su_mul (s : Kˣ) (x : Etau K τ) : (su τ s : Etau K τ) * x = (s : K) • x := by
  simp [su, Algebra.smul_def]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[sc_val]`. Express the relevant statement in the definitionally equal form `j0 τ (algebraMap K _ (s : K)) = _`. Rewrite using `[AlgHom.commutes, Algebra.algebraMap_eq_smul_one]`.
-/
theorem jU_su (s : Kˣ) : jU (j0 τ) (su τ s) = sc s := by
  apply Units.ext
  rw [sc_val]
  change j0 τ (algebraMap K _ (s : K)) = _
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

variable (O τ) in
def LL (g : GL (Fin 2) K) : Set (Etau K τ) :=
  {x | ∀ i, (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x) i ∈ Set.range (algebraMap O K)}

/- English proof (translation)
Establish `h : ∀ x, x ∈ LL O τ (jU (j0 τ) t * g) ↔ ((t⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x ∈ LL O τ g`. Introduce `x`. Simplify using `only [LL, Set.mem_setOf_eq]`. Rewrite using `[_root_.mul_inv_rev, ← map_inv, Units.val_mul, ← mulVec_mulVec, ← Algebra.leftMulMatrix_mulVec_repr]`. Both sides reduce to the same expression.

Use extensionality with `x`. Rewrite using `[h]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hx => ⟨_, hx, by simp⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Simplify using `using hy`.
-/
theorem lat_mul (t : (Etau K τ)ˣ) (g : GL (Fin 2) K) :
    LL O τ (jU (j0 τ) t * g) = ((t : Etau K τ) * ·) '' LL O τ g := by
  have h : ∀ x, x ∈ LL O τ (jU (j0 τ) t * g) ↔ ((t⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x ∈ LL O τ g := by
    intro x
    simp only [LL, Set.mem_setOf_eq]
    rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, ← mulVec_mulVec, ← Algebra.leftMulMatrix_mulVec_repr]
    rfl
  ext x
  rw [h]
  constructor
  · exact fun hx => ⟨_, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/- English proof (translation)
Rewrite using `[← jU_su (τ := τ), lat_mul]`. Simplify using `only [su_mul]`.
-/
theorem lat_sc (s : Kˣ) (g : GL (Fin 2) K) : LL O τ (sc s * g) = ((s : K) • ·) '' LL O τ g := by
  rw [← jU_su (τ := τ), lat_mul]
  simp only [su_mul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h s t`. Use `h (a := (b0 τ).equivFun.symm ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single t 1)) (by` as an intermediate fact. Introduce `i`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]`.

Distinguish the cases in `h : i = t`. Conclude with `⟨1, by simp [h]⟩`. Conclude with `⟨0, by simp [h]⟩) s`. Rewrite `this` using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, ← Units.val_mul]`. Simplify using `using this`.

Introduce `h x hx i`. Establish `e : ((g'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x = ((g'⁻¹ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x)`. Rewrite using `[mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right]`. Rewrite using `[e]`. Use `choose a ha using h`.

Use `choose v hv using hx`. Use `⟨a i 0 * v 0 + a i 1 * v 1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, ha, ha, hv, hv]`. Generalize the expression as in `((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x = w`. Simplify using `[mulVec, dotProduct]`.
-/
theorem lat_le {g g' : GL (Fin 2) K} : LL O τ g ⊆ LL O τ g' ↔ Ent O (g'⁻¹ * g) := by
  constructor
  · intro h s t
    have := h (a := (b0 τ).equivFun.symm ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single t 1)) (by
      intro i
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mulVec]
      by_cases h : i = t
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩) s
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, ← Units.val_mul] at this
    simpa using this
  · intro h x hx i
    have e : ((g'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x =
        ((g'⁻¹ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x) := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right]
    rw [e]
    choose a ha using h
    choose v hv using hx
    refine ⟨a i 0 * v 0 + a i 1 * v 1, ?_⟩
    rw [map_add, map_mul, map_mul, ha, ha, hv, hv]
    generalize ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x = w
    simp [mulVec, dotProduct]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[SetLike.mem_coe, B.mem_span_iff_repr_mem O, ← h]`. Both sides reduce to the same expression.
-/
theorem lat_basis [IsDomain O] [IsFractionRing O K] (B : Module.Basis (Fin 2) K (Etau K τ)) (g : GL (Fin 2) K)
    (h : ∀ x, ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (b0 τ).repr x = B.repr x) :
    LL O τ g = Submodule.span O (Set.range B) := by
  ext x
  rw [SetLike.mem_coe, B.mem_span_iff_repr_mem O, ← h]
  rfl

/- English proof (translation)
Set `B : Module.Basis (Fin 2) K (Etau K τ)` to `Module.Basis.ofEquivFun ((b0 τ).equivFun ≪≫ₗ (GeneralLinearGroup.toLin g⁻¹).toLinearEquiv)`. Establish `h` using `lat_basis (O := O) B g fun x => rfl`. Use `⟨⟨Finset.univ.image B, by rw [h]; simp⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h, Submodule.span_span_of_tower, B.span_eq]`.
-/
theorem lat_isLat [IsDomain O] [IsFractionRing O K] (g : GL (Fin 2) K) : IsLat O τ (LL O τ g) := by
  classical
  let B : Module.Basis (Fin 2) K (Etau K τ) :=
    Module.Basis.ofEquivFun ((b0 τ).equivFun ≪≫ₗ (GeneralLinearGroup.toLin g⁻¹).toLinearEquiv)
  have h := lat_basis (O := O) B g fun x => rfl
  refine ⟨⟨Finset.univ.image B, by rw [h]; simp⟩, ?_⟩
  rw [h, Submodule.span_span_of_tower, B.span_eq]

/- English proof (translation)
Take `⟨⟨s, rfl⟩, hsp⟩` from `hS`. Use `set M : Submodule O (Etau K τ) := Submodule.span O (s : Set (Etau K τ)) with hM`. Use `haveI : Submodule.IsLattice K M := ⟨⟨s, rfl⟩, hsp⟩`. Establish `hr : Module.finrank O M = 2`. Apply `Module.finrank_eq_of_rank_eq` to reduce the goal to its premises.

Rewrite using `[Submodule.IsLattice.rank' K M, ← Module.finrank_eq_rank, QuadraticAlgebra.finrank_eq_two]`. Set `b` to `Module.finBasisOfFinrankEq O M hr`. Set `B` to `b.extendOfIsLattice K`. Use `⟨⟨(b0 τ).toMatrix B, B.toMatrix (b0 τ), by simp, by simp⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[lat_basis B _ fun x => (b0 τ).toMatrix_mulVec_repr B x]`.

Establish `: Set.range B = M.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[B]`.

Rewrite using `[this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]`.
-/
theorem isLat_lat [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] {S : Set (Etau K τ)}
    (hS : IsLat O τ S) : ∃ g, S = LL O τ g := by
  obtain ⟨⟨s, rfl⟩, hsp⟩ := hS
  set M : Submodule O (Etau K τ) := Submodule.span O (s : Set (Etau K τ)) with hM
  haveI : Submodule.IsLattice K M := ⟨⟨s, rfl⟩, hsp⟩
  have hr : Module.finrank O M = 2 := by
    apply Module.finrank_eq_of_rank_eq
    rw [Submodule.IsLattice.rank' K M, ← Module.finrank_eq_rank, QuadraticAlgebra.finrank_eq_two]
  let b := Module.finBasisOfFinrankEq O M hr
  let B := b.extendOfIsLattice K
  refine ⟨⟨(b0 τ).toMatrix B, B.toMatrix (b0 τ), by simp, by simp⟩, ?_⟩
  rw [lat_basis B _ fun x => (b0 τ).toMatrix_mulVec_repr B x]
  have : Set.range B = M.subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp [B]
  rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, by simp⟩`.
-/
theorem cls_self (S : Set (Etau K τ)) : S ∈ cls τ S := ⟨1, by simp⟩

/- English proof (translation)
Use extensionality with `T`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, rfl⟩`. Conclude with `⟨r * s, by simp [← Set.image_comp, Function.comp_def, mul_smul]⟩`. Introduce and unpack `⟨r, rfl⟩`.

Conclude with `⟨r * s⁻¹, by simp [← Set.image_comp, Function.comp_def, smul_smul]⟩`.
-/
theorem cls_smul (s : Kˣ) (S : Set (Etau K τ)) : cls τ (((s : K) • ·) '' S) = cls τ S := by
  ext T
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r * s, by simp [← Set.image_comp, Function.comp_def, mul_smul]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r * s⁻¹, by simp [← Set.image_comp, Function.comp_def, smul_smul]⟩

/- English proof (translation)
Use extensionality with `T`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, rfl⟩`. Conclude with `⟨_, ⟨r, rfl⟩, by simp [← Set.image_comp, Function.comp_def]⟩`. Introduce and unpack `⟨_, ⟨r, rfl⟩, rfl⟩`.

Conclude with `⟨r, by simp [← Set.image_comp, Function.comp_def]⟩`.
-/
theorem cls_mul (t : Etau K τ) (S : Set (Etau K τ)) :
    cls τ ((t * ·) '' S) = (fun S => (t * ·) '' S) '' cls τ S := by
  ext T
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨_, ⟨r, rfl⟩, by simp [← Set.image_comp, Function.comp_def]⟩
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, by simp [← Set.image_comp, Function.comp_def]⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨s, hs⟩ : LL O τ g' ∈ cls τ (LL O τ g)` from `h ▸ cls_self _`. Rewrite `hs` using `[← lat_sc]`. Use `zk_iff.2 ⟨s, (sc s * g)⁻¹ * g', kg_of_inv (lat_le.1 hs.subset) ?_, ?_⟩` and prove the remaining obligations.

Use `lat_le.1 hs.superset` as an intermediate fact. Rewrite using `[_root_.mul_inv_rev, inv_inv]` and apply the resulting hypothesis. Rewrite using `[← mul_assoc, sc_comm s (sc s * g)⁻¹] group`. Introduce `h`. Take `⟨s, k, hk, e⟩` from `zk_iff.1 h`.

Establish `e' : (sc s * g)⁻¹ * g' = k`. Rewrite using `[sc_comm, _root_.mul_inv_rev, mul_assoc, e, inv_mul_cancel_left]`. Establish `: LL O τ g' = LL O τ (sc s * g)`. Use `Set.Subset.antisymm (lat_le.2 (e' ▸ kg_ent hk)) (lat_le.2 ?_)` and prove the remaining obligations. Use `kg_ent ((KG O K).inv_mem hk)` as an intermediate fact.

Rewrite `this` using `[← e', _root_.mul_inv_rev, inv_inv]`. Then use the resulting hypothesis. Rewrite using `[this, lat_sc, cls_smul]`.
-/
theorem cls_lat [IsFractionRing O K] {g g' : GL (Fin 2) K} :
    cls τ (LL O τ g) = cls τ (LL O τ g') ↔ g⁻¹ * g' ∈ ZK O K := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ : LL O τ g' ∈ cls τ (LL O τ g) := h ▸ cls_self _
    rw [← lat_sc] at hs
    refine zk_iff.2 ⟨s, (sc s * g)⁻¹ * g', kg_of_inv (lat_le.1 hs.subset) ?_, ?_⟩
    · have := lat_le.1 hs.superset
      rwa [_root_.mul_inv_rev, inv_inv]
    · rw [← mul_assoc, sc_comm s (sc s * g)⁻¹]
      group
  · intro h
    obtain ⟨s, k, hk, e⟩ := zk_iff.1 h
    have e' : (sc s * g)⁻¹ * g' = k := by
      rw [sc_comm, _root_.mul_inv_rev, mul_assoc, e, inv_mul_cancel_left]
    have : LL O τ g' = LL O τ (sc s * g) := by
      refine Set.Subset.antisymm (lat_le.2 (e' ▸ kg_ent hk)) (lat_le.2 ?_)
      have := kg_ent ((KG O K).inv_mem hk)
      rwa [← e', _root_.mul_inv_rev, inv_inv] at this
    rw [this, lat_sc, cls_smul]

end LL

end UpperTheory.V.Z.Sym.Loc.GL
