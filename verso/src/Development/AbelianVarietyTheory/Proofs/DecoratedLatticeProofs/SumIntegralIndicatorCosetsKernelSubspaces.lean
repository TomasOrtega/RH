import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke.CosetSub

/- English proof (translation)
Take `⟨U, hU⟩` from `W.exists_isCompl`. Take `⟨U', hU'⟩` from `W'.exists_isCompl`. Establish `h1` using `Submodule.finrank_add_eq_of_isCompl hU`. Establish `h2` using `Submodule.finrank_add_eq_of_isCompl hU'`. Establish `h3 : Module.finrank F U = Module.finrank F U'` using `by omega`.

Set `a : W ≃ₗ[F] W'` to `LinearEquiv.ofFinrankEq _ _ h`. Set `b : U ≃ₗ[F] U'` to `LinearEquiv.ofFinrankEq _ _ h3`. Set `e : V ≃ₗ[F] V` to `(Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ Submodule.prodEquivOfIsCompl W' U' hU'`. Establish `he : ∀ w : W, e w = a w`. Introduce `w`.

Simplify using `[e]`. Use `⟨e, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Use `he ⟨w, hw⟩` as an intermediate fact.

Express the relevant statement in the definitionally equal form `e w ∈ W'`. Simplify using `only at this`. Rewrite using `[this]`. Conclude with `(a ⟨w, hw⟩).2`. Introduce `w hw`.

Use `⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e _ = w`. Rewrite using `[he]`. Simplify using the standard rewrite rules.
-/
theorem exists_equiv_map_eq {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (W W' : Submodule F V)
    (h : Module.finrank F W = Module.finrank F W') :
    ∃ e : V ≃ₗ[F] V, W.map e.toLinearMap = W' := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  obtain ⟨U', hU'⟩ := W'.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hU
  have h2 := Submodule.finrank_add_eq_of_isCompl hU'
  have h3 : Module.finrank F U = Module.finrank F U' := by omega
  let a : W ≃ₗ[F] W' := LinearEquiv.ofFinrankEq _ _ h
  let b : U ≃ₗ[F] U' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[F] V := (Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ
    Submodule.prodEquivOfIsCompl W' U' hU'
  have he : ∀ w : W, e w = a w := by
    intro w
    simp [e]
  refine ⟨e, ?_⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := he ⟨w, hw⟩
    change e w ∈ W'
    simp only at this
    rw [this]
    exact (a ⟨w, hw⟩).2
  · intro w hw
    refine ⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩
    change e _ = w
    rw [he]
    simp

/- English proof (translation)
Take `⟨e, he⟩` from `exists_equiv_map_eq W W' h`. Set `M : Matrix D D (IsLocalRing.ResidueField O)` to `LinearMap.toMatrix' e.toLinearMap`. Use `choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)`. Establish `hAM : (Matrix.of A).map (IsLocalRing.residue O) = M`. Use extensionality with `i j`.

Conclude with `hA i j`. Establish `hM : M.det ≠ 0`. Establish `: M.det = LinearMap.det e.toLinearMap` using `LinearMap.det_toMatrix' _`. Rewrite using `[this]`. Conclude with `(LinearEquiv.isUnit_det' e).ne_zero`.

Establish `hu : IsUnit (Matrix.of A).det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]`. Express the relevant statement in the definitionally equal form `((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0`. Rewrite using `[hAM]`. Conclude with `hM`.

Take `⟨g, hg⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 hu`. Use `⟨g, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, hAM, ← he]`. Use `congr 1`. Conclude with `Matrix.toLin'_toMatrix' e.toLinearMap`.
-/
theorem exists_gl_map_eq (O : Type) [CommRing O] [IsLocalRing O] (D : Type) [Fintype D] [DecidableEq D]
    (W W' : Submodule (IsLocalRing.ResidueField O) (D → IsLocalRing.ResidueField O))
    (h : Module.finrank (IsLocalRing.ResidueField O) W =
      Module.finrank (IsLocalRing.ResidueField O) W') :
    ∃ g : GL D O, W.map (g.1.map (IsLocalRing.residue O)).mulVecLin = W' := by
  obtain ⟨e, he⟩ := exists_equiv_map_eq W W' h
  let M : Matrix D D (IsLocalRing.ResidueField O) := LinearMap.toMatrix' e.toLinearMap
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)
  have hAM : (Matrix.of A).map (IsLocalRing.residue O) = M := by
    ext i j
    exact hA i j
  have hM : M.det ≠ 0 := by
    have : M.det = LinearMap.det e.toLinearMap := LinearMap.det_toMatrix' _
    rw [this]
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have hu : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    change ((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0
    rw [hAM]
    exact hM
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨g, ?_⟩
  rw [hg, hAM, ← he]
  congr 1
  exact Matrix.toLin'_toMatrix' e.toLinearMap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D D' : Type} [Fintype D] [DecidableEq D]

def projE (F : Type) [Field F] (s : Finset D) : Matrix D D F := diagonal fun i => if i ∈ s then 1 else 0

/- English proof (translation)
Rewrite using `[projE, rank_diagonal]`. Rewrite using `[Fintype.card_subtype]`. Use `congr 1`. Use extensionality with `i`. Apply the tactic sequence `by_cases h : i ∈ s <;> simp [h]`.
-/
theorem rank_projE (F : Type) [Field F] (s : Finset D) : (projE F s).rank = s.card := by
  classical
  rw [projE, rank_diagonal]
  rw [Fintype.card_subtype]
  congr 1
  ext i
  by_cases h : i ∈ s <;> simp [h]

abbrev red {m n : Type} (M : Matrix m n 𝒪[k]) : Matrix m n 𝓀[k] := M.map (IsLocalRing.residue 𝒪[k])

abbrev inc {m n : Type} (M : Matrix m n 𝒪[k]) : Matrix m n k := M.map (algebraMap 𝒪[k] k)

abbrev incG (κ : GL D 𝒪[k]) : GL D k := GeneralLinearGroup.map (algebraMap 𝒪[k] k) κ

def colSp (s : Finset D) (κ : GL D 𝒪[k]) : Submodule 𝓀[k] (D → 𝓀[k]) :=
  LinearMap.range (red κ.1 * projE 𝓀[k] s).mulVecLin

/- English proof (translation)
Rewrite using `[← rank_projE 𝓀[k] s]`. Use `rank_mul_eq_right_of_isUnit_det _ _ ?_` and prove the remaining obligations. Establish `: (red κ.1).det = IsLocalRing.residue 𝒪[k] κ.1.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[this]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 κ.isUnit).map _`.
-/
theorem finrank_colSp (s : Finset D) (κ : GL D 𝒪[k]) : Module.finrank 𝓀[k] (colSp s κ) = s.card := by
  rw [← rank_projE 𝓀[k] s]
  refine rank_mul_eq_right_of_isUnit_det _ _ ?_
  have : (red κ.1).det = IsLocalRing.residue 𝒪[k] κ.1.det := (RingHom.map_det _ _).symm
  rw [this]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 κ.isUnit).map _

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_gl_map_eq 𝒪[k] D (LinearMap.range (projE 𝓀[k] s).mulVecLin) U (by rw [hU, ← rank_projE 𝓀[k] s]; rfl)`. Conclude with `⟨g, by rw [colSp, mulVecLin_mul, LinearMap.range_comp]; exact hg⟩`.
-/
theorem exists_colSp (s : Finset D) (U : Submodule 𝓀[k] (D → 𝓀[k])) (hU : Module.finrank 𝓀[k] U = s.card) :
    ∃ κ : GL D 𝒪[k], colSp s κ = U := by
  obtain ⟨g, hg⟩ := exists_gl_map_eq 𝒪[k] D (LinearMap.range (projE 𝓀[k] s).mulVecLin) U
    (by rw [hU, ← rank_projE 𝓀[k] s]; rfl)
  exact ⟨g, by rw [colSp, mulVecLin_mul, LinearMap.range_comp]; exact hg⟩

/- English proof (translation)
Rewrite using `[colSp, LinearMap.range_le_ker_iff, ← mulVecLin_mul, Matrix.mul_assoc, ← toLin'_apply', map_eq_zero_iff _ toLin'.injective]`.
-/
theorem colSp_le_ker_iff (s : Finset D) (κ : GL D 𝒪[k]) (Y : Matrix D' D 𝓀[k]) [Fintype D'] [DecidableEq D'] :
    colSp s κ ≤ LinearMap.ker Y.mulVecLin ↔ Y * red κ.1 * projE 𝓀[k] s = 0 := by
  rw [colSp, LinearMap.range_le_ker_iff, ← mulVecLin_mul, Matrix.mul_assoc, ← toLin'_apply', map_eq_zero_iff _ toLin'.injective]

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one, Valuation.mem_integer_iff, ← le_uniformizer_iff, ← hϖ, map_mul, map_inv₀, mul_inv_le_iff₀ (by rw [hϖ]; exact uniformizer_pos), one_mul]`.
-/
theorem div_mem_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (x : 𝒪[k]) :
    (x : k) * (ϖ : k)⁻¹ ∈ 𝒪[k] ↔ IsLocalRing.residue 𝒪[k] x = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one, Valuation.mem_integer_iff, ← le_uniformizer_iff, ← hϖ,
    map_mul, map_inv₀, mul_inv_le_iff₀ (by rw [hϖ]; exact uniformizer_pos), one_mul]

/- English proof (translation)
Rewrite using `[val_torusElt, projE, ← Matrix.ext_iff]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[mul_diagonal, mul_diagonal]`. Distinguish the cases in `h : j ∈ s`. Use `div_mem_iff hϖ (M i j)` as an intermediate fact.

Simplify using `only [indic, h, Pi.neg_apply, if_true, _root_.zpow_neg, zpow_one, mul_one, map_apply, Matrix.zero_apply]`. Conclude with `this`. Simplify using `only [indic, h, Pi.neg_apply, if_false, neg_zero, zpow_zero, mul_one, mul_zero, map_apply, Matrix.zero_apply, iff_true]`. Conclude with `(M i j).2`.
-/
theorem int_mul_torus_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) (M : Matrix D' D 𝒪[k]) :
    (∀ i j, (inc M * (torusElt k D ϖ (-indic s)).1) i j ∈ 𝒪[k]) ↔ red M * projE 𝓀[k] s = 0 := by
  rw [val_torusElt, projE, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [mul_diagonal, mul_diagonal]
  by_cases h : j ∈ s
  · have := div_mem_iff hϖ (M i j)
    simp only [indic, h, Pi.neg_apply, if_true, _root_.zpow_neg, zpow_one, mul_one, map_apply, Matrix.zero_apply]
    exact this
  · simp only [indic, h, Pi.neg_apply, if_false, neg_zero, zpow_zero, mul_one, mul_zero, map_apply, Matrix.zero_apply, iff_true]
    exact (M i j).2

omit [DecidableEq D] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Introduce `i j` and use `by rw [mul_apply] exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)`.
-/
theorem int_mul {m n : Type} {A : Matrix m D k} {B : Matrix D n k} (hA : ∀ i j, A i j ∈ 𝒪[k]) (hB : ∀ i j, B i j ∈ 𝒪[k]) :
    ∀ i j, (A * B) i j ∈ 𝒪[k] := fun i j => by
  rw [mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

/- English proof (translation)
Take `⟨κ, rfl⟩` from `hg`. Introduce `i j`. Conclude with `(κ.1 i j).2`.
-/
theorem int_of_KO {g : GL D k} (hg : g ∈ KO k D) : ∀ i j, g.1 i j ∈ 𝒪[k] := by
  obtain ⟨κ, rfl⟩ := hg
  intro i j
  exact (κ.1 i j).2

/- English proof (translation)
Set `A : Matrix D D 𝒪[k]` to `fun i j => ⟨_, hg i j⟩`. Set `B : Matrix D D 𝒪[k]` to `fun i j => ⟨_, hg' i j⟩`. Establish `hA : inc A = g.1` using `rfl`. Establish `hB : inc B = (g⁻¹).1` using `rfl`. Establish `inj : Function.Injective (inc : Matrix D D 𝒪[k] → Matrix D D k)` using `map_injective Subtype.val_injective`.

Establish `h1 : inc (1 : Matrix D D 𝒪[k]) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Use `⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext hA⟩` and prove the remaining obligations. Rewrite using `[h1, inc, Matrix.map_mul]`. Express the relevant statement in the definitionally equal form `g.1 * (g⁻¹).1 = 1`. Simplify using the standard rewrite rules.

Rewrite using `[h1, inc, Matrix.map_mul]`. Express the relevant statement in the definitionally equal form `(g⁻¹).1 * g.1 = 1`. Simplify using the standard rewrite rules.
-/
theorem KO_of_int {g : GL D k} (hg : ∀ i j, g.1 i j ∈ 𝒪[k]) (hg' : ∀ i j, (g⁻¹).1 i j ∈ 𝒪[k]) : g ∈ KO k D := by
  let A : Matrix D D 𝒪[k] := fun i j => ⟨_, hg i j⟩
  let B : Matrix D D 𝒪[k] := fun i j => ⟨_, hg' i j⟩
  have hA : inc A = g.1 := rfl
  have hB : inc B = (g⁻¹).1 := rfl
  have inj : Function.Injective (inc : Matrix D D 𝒪[k] → Matrix D D k) := map_injective Subtype.val_injective
  have h1 : inc (1 : Matrix D D 𝒪[k]) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext hA⟩
  · rw [h1, inc, Matrix.map_mul]
    change g.1 * (g⁻¹).1 = 1
    simp
  · rw [h1, inc, Matrix.map_mul]
    change (g⁻¹).1 * g.1 = 1
    simp

/- English proof (translation)
Use `⟨fun h => ?_, fun h => int_mul h (int_of_KO hg)⟩` and prove the remaining obligations. Use `int_mul h (int_of_KO (inv_mem hg))` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem int_mul_KO_iff {A : Matrix D' D k} {g : GL D k} (hg : g ∈ KO k D) :
    (∀ i j, (A * g.1) i j ∈ 𝒪[k]) ↔ ∀ i j, A i j ∈ 𝒪[k] := by
  refine ⟨fun h => ?_, fun h => int_mul h (int_of_KO hg)⟩
  have := int_mul h (int_of_KO (inv_mem hg))
  rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this

/- English proof (translation)
Establish `e1 : red y * red κ.1 = red (y * κ.1)` using `Matrix.map_mul.symm`. Establish `e2 : inc y * (incG κ).1 = inc (y * κ.1)` using `Matrix.map_mul.symm`. Rewrite using `[colSp_le_ker_iff, e1, ← int_mul_torus_iff hϖ, Units.val_mul, ← Matrix.mul_assoc, e2]`.
-/
theorem int_iff_colSp {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) [Fintype D'] [DecidableEq D']
    (y : Matrix D' D 𝒪[k]) (κ : GL D 𝒪[k]) :
    (∀ i j, (inc y * (incG κ * torusElt k D ϖ (-indic s)).1) i j ∈ 𝒪[k]) ↔ colSp s κ ≤ LinearMap.ker (red y).mulVecLin := by
  have e1 : red y * red κ.1 = red (y * κ.1) := Matrix.map_mul.symm
  have e2 : inc y * (incG κ).1 = inc (y * κ.1) := Matrix.map_mul.symm
  rw [colSp_le_ker_iff, e1, ← int_mul_torus_iff hϖ, Units.val_mul, ← Matrix.mul_assoc, e2]

/- English proof (translation)
Establish `e : (torusElt k D ϖ (-indic s))⁻¹ = torusElt k D ϖ (indic s)`. Rewrite using `[inv_eq_iff_mul_eq_one]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]`. Use `congr 1`.

Use extensionality with `i`. Rewrite using `[← zpow_add₀ ϖ.ne_zero]`. Simplify using the standard rewrite rules. Introduce `i j`. Rewrite using `[e, val_torusElt, diagonal_apply]`.

Establish `hlt : valuation k (ϖ : k) < 1` using `hϖ ▸ uniformizer_lt_one`. Use `split_ifs with h`. Distinguish the cases in `h' : i ∈ s`. Simplify `hlt.le` using `[indic, h', Valuation.mem_integer_iff]`. Simplify using `[indic, h']`.

Conclude with `zero_mem _`.
-/
theorem int_torus_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) :
    ∀ i j, ((torusElt k D ϖ (-indic s))⁻¹).1 i j ∈ 𝒪[k] := by
  have e : (torusElt k D ϖ (-indic s))⁻¹ = torusElt k D ϖ (indic s) := by
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    rw [Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1
    ext i
    rw [← zpow_add₀ ϖ.ne_zero]
    simp
  intro i j
  rw [e, val_torusElt, diagonal_apply]
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  split_ifs with h
  · by_cases h' : i ∈ s
    · simpa [indic, h', Valuation.mem_integer_iff] using hlt.le
    · simp [indic, h']
  · exact zero_mem _

/- English proof (translation)
Rewrite using `[_root_.mul_inv_rev, Units.val_mul]`. Conclude with `int_mul (int_torus_inv hϖ s) (int_of_KO (inv_mem hκ))`.
-/
theorem int_coset_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) {κ : GL D k} (hκ : κ ∈ KO k D) :
    ∀ i j, ((κ * torusElt k D ϖ (-indic s))⁻¹).1 i j ∈ 𝒪[k] := by
  rw [_root_.mul_inv_rev, Units.val_mul]
  exact int_mul (int_torus_inv hϖ s) (int_of_KO (inv_mem hκ))

/- English proof (translation)
Set `y : Matrix D D 𝒪[k]` to `fun i j => ⟨_, int_coset_inv hϖ s (κ := incG κ₁) ⟨κ₁, rfl⟩ i j⟩`. Establish `hy : inc y = ((incG κ₁ * torusElt k D ϖ (-indic s))⁻¹).1` using `rfl`. Rewrite using `[Units.val_mul, ← hy, int_iff_colSp hϖ]`. Use `h.trans ?_` and prove the remaining obligations. Rewrite using `[← int_iff_colSp hϖ, hy, ← Units.val_mul, inv_mul_cancel]`.

Conclude with `int_of_KO (one_mem _)`.
-/
theorem int_quot_of_le {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) (κ₁ κ₂ : GL D 𝒪[k])
    (h : colSp s κ₂ ≤ colSp s κ₁) :
    ∀ i j, ((incG κ₁ * torusElt k D ϖ (-indic s))⁻¹ * (incG κ₂ * torusElt k D ϖ (-indic s))).1 i j ∈ 𝒪[k] := by
  let y : Matrix D D 𝒪[k] := fun i j => ⟨_, int_coset_inv hϖ s (κ := incG κ₁) ⟨κ₁, rfl⟩ i j⟩
  have hy : inc y = ((incG κ₁ * torusElt k D ϖ (-indic s))⁻¹).1 := rfl
  rw [Units.val_mul, ← hy, int_iff_colSp hϖ]
  refine h.trans ?_
  rw [← int_iff_colSp hϖ, hy, ← Units.val_mul, inv_mul_cancel]
  exact int_of_KO (one_mem _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `KO_of_int (int_quot_of_le hϖ s κ₁ κ₂ h.ge) ?_` and prove the remaining obligations. Rewrite using `[_root_.mul_inv_rev, inv_inv]`. Conclude with `int_quot_of_le hϖ s κ₂ κ₁ h.le`.

Introduce `h`. Establish `key : ∀ y : Matrix D D 𝒪[k], colSp s κ₁ ≤ LinearMap.ker (red y).mulVecLin ↔ colSp s κ₂ ≤ LinearMap.ker (red y).mulVecLin`. Introduce `y`. Rewrite using `[← int_iff_colSp hϖ, ← int_iff_colSp hϖ, ← int_mul_KO_iff h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_left]`. Establish `key2 : ∀ U : Submodule 𝓀[k] (D → 𝓀[k]), ∃ y : Matrix D D 𝒪[k], LinearMap.ker (red y).mulVecLin = U`.

Introduce `U`. Take `⟨U', hU⟩` from `U.exists_isCompl`. Set `p : (D → 𝓀[k]) →ₗ[𝓀[k]] (D → 𝓀[k])` to `U'.subtype ∘ₗ Submodule.projectionOnto U' U hU.symm`. Use `choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) (LinearMap.toMatrix' p i j)`. Establish `hAM : red (Matrix.of A) = LinearMap.toMatrix' p`.

Use extensionality with `i j`. Conclude with `hA i j`. Use `⟨Matrix.of A, ?_⟩` and prove the remaining obligations. Rewrite using `[hAM, ← toLin'_apply', toLin'_toMatrix', LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot, Submodule.ker_projectionOnto]`. Apply `le_antisymm` to reduce the goal to its premises.

Take `⟨y, hy⟩` from `key2 (colSp s κ₂)`. Rewrite using `[← hy, key, hy]`. Take `⟨y, hy⟩` from `key2 (colSp s κ₁)`. Rewrite using `[← hy, ← key, hy]`.
-/
theorem colSp_eq_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) (κ₁ κ₂ : GL D 𝒪[k]) :
    colSp s κ₁ = colSp s κ₂ ↔
      (incG κ₁ * torusElt k D ϖ (-indic s))⁻¹ * (incG κ₂ * torusElt k D ϖ (-indic s)) ∈ KO k D := by
  constructor
  · intro h
    refine KO_of_int (int_quot_of_le hϖ s κ₁ κ₂ h.ge) ?_
    rw [_root_.mul_inv_rev, inv_inv]
    exact int_quot_of_le hϖ s κ₂ κ₁ h.le
  · intro h
    have key : ∀ y : Matrix D D 𝒪[k], colSp s κ₁ ≤ LinearMap.ker (red y).mulVecLin ↔
        colSp s κ₂ ≤ LinearMap.ker (red y).mulVecLin := by
      intro y
      rw [← int_iff_colSp hϖ, ← int_iff_colSp hϖ, ← int_mul_KO_iff h, Matrix.mul_assoc, ← Units.val_mul,
        mul_inv_cancel_left]
    have key2 : ∀ U : Submodule 𝓀[k] (D → 𝓀[k]), ∃ y : Matrix D D 𝒪[k], LinearMap.ker (red y).mulVecLin = U := by
      intro U
      obtain ⟨U', hU⟩ := U.exists_isCompl
      let p : (D → 𝓀[k]) →ₗ[𝓀[k]] (D → 𝓀[k]) := U'.subtype ∘ₗ Submodule.projectionOnto U' U hU.symm
      choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) (LinearMap.toMatrix' p i j)
      have hAM : red (Matrix.of A) = LinearMap.toMatrix' p := by
        ext i j
        exact hA i j
      refine ⟨Matrix.of A, ?_⟩
      rw [hAM, ← toLin'_apply', toLin'_toMatrix', LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot,
        Submodule.ker_projectionOnto]
    apply le_antisymm
    · obtain ⟨y, hy⟩ := key2 (colSp s κ₂)
      rw [← hy, key, hy]
    · obtain ⟨y, hy⟩ := key2 (colSp s κ₁)
      rw [← hy, ← key, hy]

/- English proof (translation)
Introduce `k _ _ _ _ D D' _ _ _ _ ϖ hϖ s RK hR y`. Use `set g₀ := torusElt k D ϖ (-indic s) with hg₀`. Establish `hex : ∀ g : RK, ∃ κ : GL D 𝒪[k], ∃ κ' ∈ KO k D, g.1 = incG κ * g₀ * κ'`. Introduce `g`. Take `⟨_, ⟨κ, rfl⟩, κ', hκ', e⟩` from `hR.1 g.1 g.2`.

Conclude with `⟨κ, κ', hκ', e⟩`. Use `choose κ κ' hκ' hg using hex`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `Finset.sum_eq_zero fun g hgR => ?_` and prove the remaining obligations.

Rewrite using `[ParHecke.intInd, if_neg]`. Introduce `h`. Apply `hy` to reduce the goal to its premises. Establish `e : g = incG (κ ⟨g, hgR⟩) * g₀ * κ' ⟨g, hgR⟩` using `hg ⟨g, hgR⟩`. Rewrite `h` using `[e, Units.val_mul, ← Matrix.mul_assoc, int_mul_KO_iff (hκ' _)]`.

Use `int_mul h (int_coset_inv hϖ s (κ := incG (κ ⟨g, hgR⟩)) ⟨_, rfl⟩)` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Then use the resulting hypothesis. Introduce and unpack `y₀ rfl`. Establish `hint : ∀ g : RK, (∀ i j, (inc y₀ * g.1.1) i j ∈ 𝒪[k]) ↔ colSp s (κ g) ≤ LinearMap.ker (red y₀).mulVecLin`. Introduce `g`.

Rewrite using `[← int_iff_colSp hϖ, hg g, Units.val_mul, ← Matrix.mul_assoc, int_mul_KO_iff (hκ' g)]`. Establish `hco : ∀ (g : RK) (c : GL D 𝒪[k]), g.1⁻¹ * (incG c * g₀) ∈ KO k D ↔ colSp s (κ g) = colSp s c`. Introduce `g c`. Rewrite using `[colSp_eq_iff hϖ, hg g, _root_.mul_inv_rev, mul_assoc, (KO k D).mul_mem_cancel_left (inv_mem (hκ' g))]`. Set `f : {g : RK // ∀ i j, (inc y₀ * g.1.1) i j ∈ 𝒪[k]} → {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = s.card}` to `fun g => ⟨colSp s (κ g.1), (hint g.1).1 g.2, finrank_colSp s _⟩`.

Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `g₁ g₂ h`. Establish `h' : colSp s (κ g₁.1) = colSp s (κ g₂.1)` using `congrArg Subtype.val h`. Use `(hR.2 (incG (κ g₂.1)) ⟨_, rfl⟩).unique ⟨g₁.1.2, (hco _ _).2 h'⟩ ⟨g₂.1.2, (hco _ _).2 rfl⟩` as an intermediate fact.

Conclude with `Subtype.ext (Subtype.ext this)`. Introduce and unpack `⟨U, hU, hd⟩`. Take `⟨c, rfl⟩` from `exists_colSp s U hd`. Take `⟨g, ⟨hgR, hgc⟩, -⟩` from `hR.2 (incG c) ⟨_, rfl⟩`. Establish `e` using `(hco ⟨g, hgR⟩ c).1 hgc`.

Conclude with `⟨⟨⟨g, hgR⟩, (hint _).2 (e ▸ hU)⟩, Subtype.ext e⟩`. Rewrite using `[← Nat.card_eq_of_bijective f hf, ← Finset.sum_coe_sort, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Simplify using `only [ParHecke.intInd]`. Rewrite using `[Finset.sum_boole]`.
-/
theorem sum_intInd_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) RK, IsRepsK (torusElt k D ϖ (-indic s)) RK → ∀ y : Matrix D' D k, ((¬ ∀ i j, y i j ∈ 𝒪[k]) → ∑ g ∈ RK, ParHecke.intInd (y * g.1) = 0) ∧ ∀ y₀ : Matrix D' D 𝒪[k], y = y₀.map (algebraMap 𝒪[k] k) → ∑ g ∈ RK, ParHecke.intInd (y * g.1) = (Nat.card {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = s.card} : ℂ) := by
  intro k _ _ _ _ D D' _ _ _ _ ϖ hϖ s RK hR y
  classical
  set g₀ := torusElt k D ϖ (-indic s) with hg₀
  have hex : ∀ g : RK, ∃ κ : GL D 𝒪[k], ∃ κ' ∈ KO k D, g.1 = incG κ * g₀ * κ' := by
    intro g
    obtain ⟨_, ⟨κ, rfl⟩, κ', hκ', e⟩ := hR.1 g.1 g.2
    exact ⟨κ, κ', hκ', e⟩
  choose κ κ' hκ' hg using hex
  constructor
  · intro hy
    refine Finset.sum_eq_zero fun g hgR => ?_
    rw [ParHecke.intInd, if_neg]
    intro h
    apply hy
    have e : g = incG (κ ⟨g, hgR⟩) * g₀ * κ' ⟨g, hgR⟩ := hg ⟨g, hgR⟩
    rw [e, Units.val_mul, ← Matrix.mul_assoc, int_mul_KO_iff (hκ' _)] at h
    have := int_mul h (int_coset_inv hϖ s (κ := incG (κ ⟨g, hgR⟩)) ⟨_, rfl⟩)
    rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
  · rintro y₀ rfl
    have hint : ∀ g : RK, (∀ i j, (inc y₀ * g.1.1) i j ∈ 𝒪[k]) ↔ colSp s (κ g) ≤ LinearMap.ker (red y₀).mulVecLin := by
      intro g
      rw [← int_iff_colSp hϖ, hg g, Units.val_mul, ← Matrix.mul_assoc, int_mul_KO_iff (hκ' g)]
    have hco : ∀ (g : RK) (c : GL D 𝒪[k]), g.1⁻¹ * (incG c * g₀) ∈ KO k D ↔ colSp s (κ g) = colSp s c := by
      intro g c
      rw [colSp_eq_iff hϖ, hg g, _root_.mul_inv_rev, mul_assoc, (KO k D).mul_mem_cancel_left (inv_mem (hκ' g))]
    let f : {g : RK // ∀ i j, (inc y₀ * g.1.1) i j ∈ 𝒪[k]} → {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = s.card} :=
      fun g => ⟨colSp s (κ g.1), (hint g.1).1 g.2, finrank_colSp s _⟩
    have hf : Function.Bijective f := by
      constructor
      · intro g₁ g₂ h
        have h' : colSp s (κ g₁.1) = colSp s (κ g₂.1) := congrArg Subtype.val h
        have := (hR.2 (incG (κ g₂.1)) ⟨_, rfl⟩).unique ⟨g₁.1.2, (hco _ _).2 h'⟩ ⟨g₂.1.2, (hco _ _).2 rfl⟩
        exact Subtype.ext (Subtype.ext this)
      · rintro ⟨U, hU, hd⟩
        obtain ⟨c, rfl⟩ := exists_colSp s U hd
        obtain ⟨g, ⟨hgR, hgc⟩, -⟩ := hR.2 (incG c) ⟨_, rfl⟩
        have e := (hco ⟨g, hgR⟩ c).1 hgc
        exact ⟨⟨⟨g, hgR⟩, (hint _).2 (e ▸ hU)⟩, Subtype.ext e⟩
    rw [← Nat.card_eq_of_bijective f hf, ← Finset.sum_coe_sort, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [ParHecke.intInd]
    rw [Finset.sum_boole]

end GlobalTheory.ParHecke.CosetSub

end
