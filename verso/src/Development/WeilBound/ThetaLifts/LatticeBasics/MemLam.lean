import Mathlib

noncomputable section

namespace GlobalTheory.ThK.Dbl.Bmp

open Matrix

variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]

/- English proof (translation)
Use `haveI : Module.Free O L := Submodule.IsLattice.free K L`. Set `b` to `Module.Free.chooseBasis O L`. Set `v : Module.Free.ChooseBasisIndex O L → V` to `fun i => (b i : V)`. Establish `hliO : LinearIndependent O v` using `b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)`. Establish `hliK : LinearIndependent K v` using `(LinearIndependent.iff_fractionRing O K).mp hliO`.

Establish `hspanO : Submodule.span O (Set.range v) = L`. Establish `hr : Set.range v = L.subtype '' Set.range b` using `by rw [← Set.range_comp]; rfl`. Rewrite using `[hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `hspK : ⊤ ≤ Submodule.span K (Set.range v)`. Rewrite using `[← Submodule.IsLattice.span_eq_top (A := K) (M := L)]`.

Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce `z hz`. Establish `hz' : z ∈ Submodule.span O (Set.range v)` using `by rw [hspanO]; exact hz`. Conclude with `Submodule.span_le_restrictScalars O K _ hz'`. Set `bK` to `Module.Basis.mk hliK hspK`.

Establish `hrange : Set.range bK = Set.range v`. Use extensionality with `z`. Simplify using `only [Set.mem_range, bK, Module.Basis.mk_apply]`. Establish `hmem : ∀ z, z ∈ L ↔ ∀ i, bK.repr z i ∈ Set.range (algebraMap O K)`. Introduce `z`.

Rewrite using `[← Module.Basis.mem_span_iff_repr_mem O bK z, hrange, hspanO]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, bK.repr y i ∉ Set.range (algebraMap O K) := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hy ((hmem y).mpr hcon)`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : O, ψ (bK.repr y i * algebraMap O K t) ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hi ((hψ _).mp hcon)`. Establish `hψO : ∀ o : O, ψ (algebraMap O K o) = 1` using `fun o => by`.

Establish `h1` using `((hψ (algebraMap O K o)).mpr ⟨o, rfl⟩) 1`. Simplify using `using h1`. Use `⟨algebraMap O K t • bK.coord i, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨o, ho⟩` from `(hmem z).mp hz i`.

Simplify using `only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]`. Rewrite using `[← ho, ← map_mul]`. Conclude with `hψO _`. Simplify using `only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]`. Rewrite using `[mul_comm]` and apply the resulting hypothesis.
-/
theorem sep (ψ : AddChar K ℂ) (hψ : ∀ x, (∀ y : O, ψ (x * algebraMap O K y) = 1) ↔ x ∈ (algebraMap O K).range)
    {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (L : Submodule O V) [L.IsLattice K] {y : V}
    (hy : y ∉ L) : ∃ l : V →ₗ[K] K, (∀ z ∈ L, ψ (l z) = 1) ∧ ψ (l y) ≠ 1 := by
  classical
  haveI : Module.Free O L := Submodule.IsLattice.free K L
  let b := Module.Free.chooseBasis O L
  let v : Module.Free.ChooseBasisIndex O L → V := fun i => (b i : V)
  have hliO : LinearIndependent O v := b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliK : LinearIndependent K v := (LinearIndependent.iff_fractionRing O K).mp hliO
  have hspanO : Submodule.span O (Set.range v) = L := by
    have hr : Set.range v = L.subtype '' Set.range b := by rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspK : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← Submodule.IsLattice.span_eq_top (A := K) (M := L)]
    apply Submodule.span_le.mpr
    intro z hz
    have hz' : z ∈ Submodule.span O (Set.range v) := by rw [hspanO]; exact hz
    exact Submodule.span_le_restrictScalars O K _ hz'
  let bK := Module.Basis.mk hliK hspK
  have hrange : Set.range bK = Set.range v := by
    ext z
    simp only [Set.mem_range, bK, Module.Basis.mk_apply]
  have hmem : ∀ z, z ∈ L ↔ ∀ i, bK.repr z i ∈ Set.range (algebraMap O K) := by
    intro z
    rw [← Module.Basis.mem_span_iff_repr_mem O bK z, hrange, hspanO]
  obtain ⟨i, hi⟩ : ∃ i, bK.repr y i ∉ Set.range (algebraMap O K) := by
    by_contra hcon
    push_neg at hcon
    exact hy ((hmem y).mpr hcon)
  obtain ⟨t, ht⟩ : ∃ t : O, ψ (bK.repr y i * algebraMap O K t) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hi ((hψ _).mp hcon)
  have hψO : ∀ o : O, ψ (algebraMap O K o) = 1 := fun o => by
    have h1 := ((hψ (algebraMap O K o)).mpr ⟨o, rfl⟩) 1
    simpa using h1
  refine ⟨algebraMap O K t • bK.coord i, ?_, ?_⟩
  · intro z hz
    obtain ⟨o, ho⟩ := (hmem z).mp hz i
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    rw [← ho, ← map_mul]
    exact hψO _
  · simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    rwa [mul_comm]

variable (K) in

def lam (a : O) (m m' : ℕ) : Submodule O (Matrix (Fin m) (Fin m') K) :=
  LinearMap.range (a • (Algebra.linearMap O K).mapMatrix)

variable {a : O} {n d : ℕ}

omit [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O K] in
/- English proof (translation)
Simplify using `only [lam, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.mapMatrix_apply, Algebra.coe_linearMap]`.
-/
theorem mem_lam {Y : Matrix (Fin n) (Fin d) K} : Y ∈ lam K a n d ↔ ∃ α : Matrix (Fin n) (Fin d) O, a • α.map (algebraMap O K) = Y := by
  simp only [lam, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.mapMatrix_apply, Algebra.coe_linearMap]

omit [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O K] in
/- English proof (translation)
Rewrite `hh`, `hY`, the goal using `[mem_lam]`. Take `⟨α, hα⟩` from `hh`. Take `⟨β, hβ⟩` from `hY`. Establish `hf : ∀ x : O, algebraMap O K (a • x) = a • algebraMap O K x` using `fun x => by`. Rewrite using `[smul_eq_mul, map_mul, Algebra.smul_def]`.

Use `⟨β + α * y + a • (α * β), ?_⟩` and prove the remaining obligations. Establish `e1 : h = 1 + a • α.map (algebraMap O K)` using `by rw [hα]; abel`. Establish `e2 : Y = y.map (algebraMap O K) + a • β.map (algebraMap O K)` using `by rw [hβ]; abel`. Rewrite using `[e1, e2, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_smul (algebraMap O K) a hf, Matrix.map_mul, Matrix.map_mul]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_add]`.

Normalize the expressions using the abelian group laws.
-/
theorem keep {h : Matrix (Fin n) (Fin n) K} (hh : h - 1 ∈ lam K a n n) (y : Matrix (Fin n) (Fin d) O) {Y : Matrix (Fin n) (Fin d) K}
    (hY : Y - y.map (algebraMap O K) ∈ lam K a n d) : h * Y - y.map (algebraMap O K) ∈ lam K a n d := by
  rw [mem_lam] at hh hY ⊢
  obtain ⟨α, hα⟩ := hh
  obtain ⟨β, hβ⟩ := hY
  have hf : ∀ x : O, algebraMap O K (a • x) = a • algebraMap O K x := fun x => by
    rw [smul_eq_mul, map_mul, Algebra.smul_def]
  refine ⟨β + α * y + a • (α * β), ?_⟩
  have e1 : h = 1 + a • α.map (algebraMap O K) := by rw [hα]; abel
  have e2 : Y = y.map (algebraMap O K) + a • β.map (algebraMap O K) := by rw [hβ]; abel
  rw [e1, e2, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_smul (algebraMap O K) a hf, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_add]
  abel

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `lam`. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map _`. Rewrite using `[eq_top_iff]`.

Introduce `Y _`. Rewrite using `[Matrix.matrix_eq_sum_single Y]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `hmem : a • (Matrix.single i j (1 : O)).map (algebraMap O K) ∈ lam K a n d` using `mem_lam.mpr ⟨_, rfl⟩`. Establish `hne : algebraMap O K a ≠ 0` using `fun hz => h0 ((IsFractionRing.injective O K) (by rw [hz, map_zero]))`.

Establish `hrw : Matrix.single i j (Y i j) = (Y i j * (algebraMap O K a)⁻¹) • (a • (Matrix.single i j (1 : O)).map (algebraMap O K))`. Rewrite using `[Matrix.map_single, map_one, ← algebraMap_smul K a, smul_smul, inv_mul_cancel_right₀ hne, Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[hrw]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
private theorem isLattice_lam_of_ne_zero [IsFractionRing O K] {a : O} {n d : ℕ} (h0 : a ≠ 0) :
    (lam K a n d).IsLattice K := by
  classical
  refine ⟨?_, ?_⟩
  · unfold lam
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · rw [eq_top_iff]
    intro Y _
    rw [Matrix.matrix_eq_sum_single Y]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have hmem : a • (Matrix.single i j (1 : O)).map (algebraMap O K) ∈ lam K a n d :=
      mem_lam.mpr ⟨_, rfl⟩
    have hne : algebraMap O K a ≠ 0 := fun hz =>
      h0 ((IsFractionRing.injective O K) (by rw [hz, map_zero]))
    have hrw : Matrix.single i j (Y i j) =
        (Y i j * (algebraMap O K a)⁻¹) • (a • (Matrix.single i j (1 : O)).map (algebraMap O K)) := by
      rw [Matrix.map_single, map_one, ← algebraMap_smul K a, smul_smul, inv_mul_cancel_right₀ hne,
        Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hrw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/- English proof (translation)
Use `⟨(Submodule.IsLattice.fg (A := K) (M := L)).map _, ?_⟩` and prove the remaining obligations. Establish `himg : ((L.map (G.restrictScalars O) : Submodule O (Matrix (Fin n) (Fin d) K)) : Set (Matrix (Fin n) (Fin d) K)) = G '' (L : Set (Matrix (Fin n) (Fin d) K))`. Rewrite using `[Submodule.map_coe]`. Both sides reduce to the same expression. Rewrite using `[himg, Submodule.span_image, Submodule.IsLattice.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr hG]`.
-/
private theorem isLattice_map_of_surjective {n d : ℕ} (L : Submodule O (Matrix (Fin n) (Fin d) K)) [L.IsLattice K]
    (G : Matrix (Fin n) (Fin d) K →ₗ[K] Matrix (Fin n) (Fin d) K) (hG : Function.Surjective G) :
    (L.map (G.restrictScalars O)).IsLattice K := by
  refine ⟨(Submodule.IsLattice.fg (A := K) (M := L)).map _, ?_⟩
  have himg : ((L.map (G.restrictScalars O) : Submodule O (Matrix (Fin n) (Fin d) K)) :
      Set (Matrix (Fin n) (Fin d) K)) = G '' (L : Set (Matrix (Fin n) (Fin d) K)) := by
    rw [Submodule.map_coe]
    rfl
  rw [himg, Submodule.span_image, Submodule.IsLattice.span_eq_top, Submodule.map_top,
    LinearMap.range_eq_top.mpr hG]

/- English proof (translation)
Rewrite using `[← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]`. Establish `hπa : IsLocalRing.residue O a = 0` using `(IsLocalRing.residue_eq_zero_iff a).mpr ha`. Establish `hone : (IsLocalRing.residue O).mapMatrix (1 + a • M) = 1`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply, hπa, apply_ite]`.

Rewrite using `[hone, Matrix.det_one]`. Conclude with `one_ne_zero`.
-/
private theorem isUnit_det_lemma_3 [IsLocalRing O] {a : O} {n : ℕ} (ha : a ∈ IsLocalRing.maximalIdeal O)
    (M : Matrix (Fin n) (Fin n) O) : IsUnit (1 + a • M).det := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
  have hπa : IsLocalRing.residue O a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
  have hone : (IsLocalRing.residue O).mapMatrix (1 + a • M) = 1 := by
    ext i j
    simp [Matrix.one_apply, hπa, apply_ite]
  rw [hone, Matrix.det_one]
  exact one_ne_zero

/- English proof (translation)
Establish `hf : ∀ x : O, algebraMap O K (a • x) = a • algebraMap O K x` using `fun x => by`. Rewrite using `[smul_eq_mul, map_mul, Algebra.smul_def]`. Establish `hm1 : (1 : Matrix (Fin n) (Fin n) O).map (algebraMap O K) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Set `G : Matrix (Fin n) (Fin d) K →ₗ[K] Matrix (Fin n) (Fin d) K` to `{ toFun := fun Y => h.1 * Y map_add' := Matrix.mul_add _ map_smul' := fun c Y => by simp [Matrix.mul_smul] }`. Establish `hGs : Function.Surjective G` using `fun Y => ⟨(h⁻¹).1 * Y, by show h.1 * ((h⁻¹).1 * Y) = Y`.

Rewrite using `[← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩`. Use `haveI : (lam K a n d).IsLattice K := isLattice_lam_of_ne_zero h0`. Use `haveI : ((lam K a n d).map (G.restrictScalars O)).IsLattice K := isLattice_map_of_surjective _ G hGs`. Use `haveI : ((lam K a n d) ⊔ (lam K a n d).map (G.restrictScalars O)).IsLattice K := Submodule.IsLattice.sup K _ _`. Distinguish the cases in `hmem : h.1 * y.map (algebraMap O K) - y.map (algebraMap O K) ∈ (lam K a n d) ⊔ (lam K a n d).map (G.restrictScalars O)`.

Use `left`. Take `⟨Y1, hY1, Z, hZ, hsum⟩` from `Submodule.mem_sup.mp hmem`. Take `⟨Y2, hY2, rfl⟩` from `Submodule.mem_map.mp hZ`. Take `⟨A1, rfl⟩` from `mem_lam.mp hY1`. Take `⟨A2, rfl⟩` from `mem_lam.mp hY2`.

Express the relevant statement in the definitionally equal form `a • A1.map (algebraMap O K) + h.1 * (a • A2.map (algebraMap O K)) = h.1 * y.map (algebraMap O K) - y.map (algebraMap O K) at hsum`. Establish `hyr : y.map (algebraMap O K) * r.map (algebraMap O K) = 1`. Rewrite using `[← Matrix.map_mul, hr, hm1]`. Establish `e : a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) + a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K))) = h.1 - 1`. Establish `h2` using `congrArg (fun M => M * r.map (algebraMap O K)) hsum`.

Simplify using `only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hyr, Matrix.mul_one, Matrix.one_mul] at h2`. Conclude with `h2`. Set `P : Matrix (Fin n) (Fin n) O` to `1 + a • (-(A2 * r))`. Set `Q : Matrix (Fin n) (Fin n) O` to `1 + a • (A1 * r)`. Establish `hPm : P.map (algebraMap O K) = 1 - a • (A2.map (algebraMap O K) * r.map (algebraMap O K))`.

Simplify using `only [P, Q]`. Rewrite using `[Matrix.map_add _ (map_add _), hm1, Matrix.map_smul _ a hf, Matrix.map_neg _ (map_neg _), Matrix.map_mul, smul_neg, sub_eq_add_neg]`. Establish `hQm : Q.map (algebraMap O K) = 1 + a • (A1.map (algebraMap O K) * r.map (algebraMap O K))`. Simplify using `only [Q]`. Rewrite using `[Matrix.map_add _ (map_add _), hm1, Matrix.map_smul _ a hf, Matrix.map_mul]`.

Establish `key : h.1 * P.map (algebraMap O K) = Q.map (algebraMap O K)`. Rewrite using `[hPm, hQm, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hPu : IsUnit P.det` using `isUnit_det_lemma_3 ha _`. Establish `hQu : IsUnit Q.det` using `isUnit_det_lemma_3 ha _`.

Establish `hPi : P.map (algebraMap O K) * P⁻¹.map (algebraMap O K) = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv P hPu, hm1]`. Establish `hQi : Q.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv Q hQu, hm1]`. Establish `hh : h.1 = Q.map (algebraMap O K) * P⁻¹.map (algebraMap O K)`.

Combine the equalities or inequalities in the displayed calculation. Establish `key2 : (h⁻¹).1 * Q.map (algebraMap O K) = P.map (algebraMap O K)`. Rewrite using `[← key, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Establish `hhi : (h⁻¹).1 = P.map (algebraMap O K) * Q⁻¹.map (algebraMap O K)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hQi, Matrix.mul_one]`. Use `_ = P.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) := by rw [← Matrix.mul_assoc, key2]`. Establish `hQP : Q - P = a • (A1 * r + A2 * r)`. Simplify using `only [P, Q, smul_add, smul_neg]`. Normalize the expressions using the abelian group laws.

Establish `hPQ : P - Q = a • (-(A1 * r + A2 * r))`. Rewrite using `[← neg_sub, hQP, smul_neg]`. Use `⟨mem_lam.mpr ⟨(A1 * r + A2 * r) * P⁻¹, ?_⟩, mem_lam.mpr ⟨-(A1 * r + A2 * r) * Q⁻¹, ?_⟩⟩` and prove the remaining obligations. Establish `hd : h.1 - 1 = (Q - P).map (algebraMap O K) * P⁻¹.map (algebraMap O K)`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.sub_mul, hPi, ← hh]`.

Rewrite using `[hd, hQP, Matrix.map_smul _ a hf, Matrix.smul_mul, Matrix.map_mul]`. Establish `hd : (h⁻¹).1 - 1 = (P - Q).map (algebraMap O K) * Q⁻¹.map (algebraMap O K)`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.sub_mul, hQi, ← hhi]`. Rewrite using `[hd, hPQ, Matrix.map_smul _ a hf, Matrix.smul_mul, Matrix.map_mul]`. Use `right`.

Take `⟨l, hl1, hl2⟩` from `sep ψ hψ _ hmem`. Conclude with `⟨l, fun Y hY => ⟨hl1 Y (Submodule.mem_sup_left hY), hl1 _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem hY))⟩, hl2⟩`.
-/
theorem dich [IsLocalRing O] (ψ : AddChar K ℂ) (hψ : ∀ x, (∀ y : O, ψ (x * algebraMap O K y) = 1) ↔ x ∈ (algebraMap O K).range)
    (h0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal O) (y : Matrix (Fin n) (Fin d) O) (r : Matrix (Fin d) (Fin n) O) (hr : y * r = 1)
    (h : GL (Fin n) K) : (h.1 - 1 ∈ lam K a n n ∧ (h⁻¹).1 - 1 ∈ lam K a n n) ∨ ∃ l : Matrix (Fin n) (Fin d) K →ₗ[K] K,
      (∀ Y ∈ lam K a n d, ψ (l Y) = 1 ∧ ψ (l (h.1 * Y)) = 1) ∧ ψ (l (h.1 * y.map (algebraMap O K) - y.map (algebraMap O K))) ≠ 1 := by
  classical
  have hf : ∀ x : O, algebraMap O K (a • x) = a • algebraMap O K x := fun x => by
    rw [smul_eq_mul, map_mul, Algebra.smul_def]
  have hm1 : (1 : Matrix (Fin n) (Fin n) O).map (algebraMap O K) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  let G : Matrix (Fin n) (Fin d) K →ₗ[K] Matrix (Fin n) (Fin d) K :=
    { toFun := fun Y => h.1 * Y
      map_add' := Matrix.mul_add _
      map_smul' := fun c Y => by simp [Matrix.mul_smul] }
  have hGs : Function.Surjective G := fun Y =>
    ⟨(h⁻¹).1 * Y, by
      show h.1 * ((h⁻¹).1 * Y) = Y
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩
  haveI : (lam K a n d).IsLattice K := isLattice_lam_of_ne_zero h0
  haveI : ((lam K a n d).map (G.restrictScalars O)).IsLattice K := isLattice_map_of_surjective _ G hGs
  haveI : ((lam K a n d) ⊔ (lam K a n d).map (G.restrictScalars O)).IsLattice K :=
    Submodule.IsLattice.sup K _ _
  by_cases hmem : h.1 * y.map (algebraMap O K) - y.map (algebraMap O K) ∈
      (lam K a n d) ⊔ (lam K a n d).map (G.restrictScalars O)
  · left
    obtain ⟨Y1, hY1, Z, hZ, hsum⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨Y2, hY2, rfl⟩ := Submodule.mem_map.mp hZ
    obtain ⟨A1, rfl⟩ := mem_lam.mp hY1
    obtain ⟨A2, rfl⟩ := mem_lam.mp hY2
    change a • A1.map (algebraMap O K) + h.1 * (a • A2.map (algebraMap O K)) =
      h.1 * y.map (algebraMap O K) - y.map (algebraMap O K) at hsum
    have hyr : y.map (algebraMap O K) * r.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, hr, hm1]
    have e : a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) +
        a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K))) = h.1 - 1 := by
      have h2 := congrArg (fun M => M * r.map (algebraMap O K)) hsum
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hyr,
        Matrix.mul_one, Matrix.one_mul] at h2
      exact h2
    let P : Matrix (Fin n) (Fin n) O := 1 + a • (-(A2 * r))
    let Q : Matrix (Fin n) (Fin n) O := 1 + a • (A1 * r)
    have hPm : P.map (algebraMap O K) = 1 - a • (A2.map (algebraMap O K) * r.map (algebraMap O K)) := by
      simp only [P, Q]
      rw [Matrix.map_add _ (map_add _), hm1, Matrix.map_smul _ a hf, Matrix.map_neg _ (map_neg _),
        Matrix.map_mul, smul_neg, sub_eq_add_neg]
    have hQm : Q.map (algebraMap O K) = 1 + a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) := by
      simp only [Q]
      rw [Matrix.map_add _ (map_add _), hm1, Matrix.map_smul _ a hf, Matrix.map_mul]
    have key : h.1 * P.map (algebraMap O K) = Q.map (algebraMap O K) := by
      rw [hPm, hQm, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
      calc h.1 - a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K)))
          = (h.1 - 1) - a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K))) + 1 := by abel
        _ = (a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) +
              a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K)))) -
              a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K))) + 1 := by rw [e]
        _ = 1 + a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) := by abel
    have hPu : IsUnit P.det := isUnit_det_lemma_3 ha _
    have hQu : IsUnit Q.det := isUnit_det_lemma_3 ha _
    have hPi : P.map (algebraMap O K) * P⁻¹.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv P hPu, hm1]
    have hQi : Q.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv Q hQu, hm1]
    have hh : h.1 = Q.map (algebraMap O K) * P⁻¹.map (algebraMap O K) := by
      calc h.1 = h.1 * (P.map (algebraMap O K) * P⁻¹.map (algebraMap O K)) := by rw [hPi, Matrix.mul_one]
        _ = Q.map (algebraMap O K) * P⁻¹.map (algebraMap O K) := by rw [← Matrix.mul_assoc, key]
    have key2 : (h⁻¹).1 * Q.map (algebraMap O K) = P.map (algebraMap O K) := by
      rw [← key, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hhi : (h⁻¹).1 = P.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) := by
      calc (h⁻¹).1 = (h⁻¹).1 * (Q.map (algebraMap O K) * Q⁻¹.map (algebraMap O K)) := by
            rw [hQi, Matrix.mul_one]
        _ = P.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) := by rw [← Matrix.mul_assoc, key2]
    have hQP : Q - P = a • (A1 * r + A2 * r) := by
      simp only [P, Q, smul_add, smul_neg]
      abel
    have hPQ : P - Q = a • (-(A1 * r + A2 * r)) := by
      rw [← neg_sub, hQP, smul_neg]
    refine ⟨mem_lam.mpr ⟨(A1 * r + A2 * r) * P⁻¹, ?_⟩, mem_lam.mpr ⟨-(A1 * r + A2 * r) * Q⁻¹, ?_⟩⟩
    · have hd : h.1 - 1 = (Q - P).map (algebraMap O K) * P⁻¹.map (algebraMap O K) := by
        rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, hPi, ← hh]
      rw [hd, hQP, Matrix.map_smul _ a hf, Matrix.smul_mul, Matrix.map_mul]
    · have hd : (h⁻¹).1 - 1 = (P - Q).map (algebraMap O K) * Q⁻¹.map (algebraMap O K) := by
        rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, hQi, ← hhi]
      rw [hd, hPQ, Matrix.map_smul _ a hf, Matrix.smul_mul, Matrix.map_mul]
  · right
    obtain ⟨l, hl1, hl2⟩ := sep ψ hψ _ hmem
    exact ⟨l, fun Y hY => ⟨hl1 Y (Submodule.mem_sup_left hY),
      hl1 _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem hY))⟩, hl2⟩

end GlobalTheory.ThK.Dbl.Bmp

end
