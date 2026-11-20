import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters

open Polynomial

noncomputable section

namespace GlobalTheory.CuspInv

open GlobalTheory.IndefiniteRowSideFullHecke

def mirrorEquiv (k : Type) [Field k] : k[X] ≃* k[X] where
  toFun := mirror
  invFun := mirror
  left_inv := fun f => mirror_mirror f
  right_inv := fun f => mirror_mirror f
  map_mul' := fun f g => mirror_mul_of_domain f g

/- English proof (translation)
Take `⟨φ, n, hφ, hn⟩` from `H`. Establish `hu : IsUnit h` using `(Matrix.isUnit_iff_isUnit_det h).2 (Matrix.isUnit_det_of_right_inverse hh)`. Establish `hinv : h' = h⁻¹` using `(Matrix.inv_eq_right_inv hh).symm`. Establish `hdet : h.det ≠ 0` using `(Matrix.isUnit_det_of_right_inverse hh).ne_zero`. Establish `h0 : h.charpoly.coeff 0 ≠ 0`.

Introduce `h0`. Conclude with `hdet (by rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero])`. Establish `hm : h.charpoly.mirror = h.charpolyRev`. Rewrite using `[mirror, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (p := h.charpoly) h0, pow_zero, mul_one, Matrix.reverse_charpoly]`. Establish `hψ : Irreducible (mirrorEquiv k φ)` using `(MulEquiv.irreducible_iff (mirrorEquiv k)).2 hφ`.

Establish `h1 : h.charpolyRev = (mirrorEquiv k φ) ^ n`. Rewrite using `[← map_pow, ← hn, ← hm]`. Both sides reduce to the same expression. Establish `hass : Associated h'.charpoly ((normalize (mirrorEquiv k φ)) ^ n)`. Use `Associated.trans ?_ ((associated_normalize _).pow_pow)` and prove the remaining obligations.

Rewrite using `[hinv, Matrix.charpoly_inv h hu, h1]`. Use `associated_unit_mul_left _ _ ?_` and prove the remaining obligations. Use `IsUnit.mul (IsUnit.pow _ isUnit_one.neg) ?_` and prove the remaining obligations. Rewrite using `[isUnit_C, Ring.inverse_eq_inv', isUnit_iff_ne_zero]`. Conclude with `inv_ne_zero hdet`.

Use `⟨normalize (mirrorEquiv k φ), n, (associated_normalize _).irreducible hψ, ?_⟩` and prove the remaining obligations. Conclude with `eq_of_monic_of_associated h'.charpoly_monic ((monic_normalize hψ.ne_zero).pow n) hass`.
-/
theorem powIrr_of_inv {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι] (h h' : Matrix ι ι k)
    (hh : h * h' = 1) (H : ∃ (φ : k[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n) :
    ∃ (φ : k[X]) (n : ℕ), Irreducible φ ∧ h'.charpoly = φ ^ n := by
  classical
  obtain ⟨φ, n, hφ, hn⟩ := H
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (Matrix.isUnit_det_of_right_inverse hh)
  have hinv : h' = h⁻¹ := (Matrix.inv_eq_right_inv hh).symm
  have hdet : h.det ≠ 0 := (Matrix.isUnit_det_of_right_inverse hh).ne_zero
  have h0 : h.charpoly.coeff 0 ≠ 0 := by
    intro h0
    exact hdet (by rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero])
  have hm : h.charpoly.mirror = h.charpolyRev := by
    rw [mirror, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (p := h.charpoly) h0, pow_zero, mul_one,
      Matrix.reverse_charpoly]
  have hψ : Irreducible (mirrorEquiv k φ) := (MulEquiv.irreducible_iff (mirrorEquiv k)).2 hφ
  have h1 : h.charpolyRev = (mirrorEquiv k φ) ^ n := by
    rw [← map_pow, ← hn, ← hm]; rfl
  have hass : Associated h'.charpoly ((normalize (mirrorEquiv k φ)) ^ n) := by
    refine Associated.trans ?_ ((associated_normalize _).pow_pow)
    rw [hinv, Matrix.charpoly_inv h hu, h1]
    refine associated_unit_mul_left _ _ ?_
    refine IsUnit.mul (IsUnit.pow _ isUnit_one.neg) ?_
    rw [isUnit_C, Ring.inverse_eq_inv', isUnit_iff_ne_zero]
    exact inv_ne_zero hdet
  refine ⟨normalize (mirrorEquiv k φ), n, (associated_normalize _).irreducible hψ, ?_⟩
  exact eq_of_monic_of_associated h'.charpoly_monic ((monic_normalize hψ.ne_zero).pow n) hass

/- English proof (translation)
Introduce `v hv`. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff]`. Establish `h1 : g (f v) = v` using `by rw [← Module.End.mul_apply, hfg]; rfl`. Rewrite `h1` using `[hv, map_smul]`. Distinguish the cases in `hz : z = 0`.

Substitute `hz` using the available equality. Rewrite `h1` using `[zero_smul]`. Rewrite using `[← h1]`. Simplify using the standard rewrite rules. Use `conv_rhs => rw [← h1]`.

Rewrite using `[smul_smul, inv_mul_cancel₀ hz, one_smul]`.
-/
theorem eigenspace_le {L V : Type} [Field L] [AddCommGroup V] [Module L V] (f g : Module.End L V)
    (hfg : g * f = 1) (z : L) : f.eigenspace z ≤ g.eigenspace z⁻¹ := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : g (f v) = v := by rw [← Module.End.mul_apply, hfg]; rfl
  rw [hv, map_smul] at h1
  by_cases hz : z = 0
  · subst hz
    rw [zero_smul] at h1
    rw [← h1]; simp
  · conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul]

/- English proof (translation)
Use `le_antisymm ?_ (eigenspace_le f g hgf z)` and prove the remaining obligations. Simplify using `using eigenspace_le g f hfg z⁻¹`.
-/
theorem eigenspace_inv {L V : Type} [Field L] [AddCommGroup V] [Module L V] (f g : Module.End L V)
    (hfg : f * g = 1) (hgf : g * f = 1) (z : L) : g.eigenspace z⁻¹ = f.eigenspace z := by
  refine le_antisymm ?_ (eigenspace_le f g hgf z)
  simpa using eigenspace_le g f hfg z⁻¹

/- English proof (translation)
Rewrite using `[← Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', Matrix.charpoly_map, mem_aroots, IsRoot, eval_map_algebraMap]`. Simplify using `[h.charpoly_monic.ne_zero]`.
-/
theorem mem_aroots_iff {k L ι : Type} [Field k] [Field L] [Algebra k L] [Fintype ι] [DecidableEq ι]
    (h : Matrix ι ι k) (z : L) :
    z ∈ h.charpoly.aroots L ↔
      Module.End.eigenspace (Matrix.toLin' (h.map (algebraMap k L))) z ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Matrix.charpoly_toLin', Matrix.charpoly_map, mem_aroots, IsRoot, eval_map_algebraMap]
  simp [h.charpoly_monic.ne_zero]

/- English proof (translation)
Establish `hinj : Function.Injective (fun u : LevelCuspCharacters.Tor p d => ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p))` using `fun a b hab => Subtype.ext (Units.ext hab)`. Unfold `LevelCuspCharacters.torVal`. Distinguish the cases in `hz : ∃ u : LevelCuspCharacters.Tor p d, ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) = z`. Take `⟨u, rfl⟩` from `hz`. Establish `h2 : (((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p))⁻¹ = (((u⁻¹ : LevelCuspCharacters.Tor p d) : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p)` using `by simp`.

Rewrite using `[h2, hinj.extend_apply, hinj.extend_apply]`. Simplify using the standard rewrite rules. Rewrite using `[Function.extend_apply' _ _ _ hz, Function.extend_apply']`. Both sides reduce to the same expression. Introduce and unpack `⟨u, hu⟩`.

Conclude with `hz ⟨u⁻¹, by simp [hu]⟩`.
-/
theorem torVal_inv {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {d : ℕ} (θ : LevelCuspCharacters.Tor p d →* Kˣ)
    (z : LevelCuspCharacters.Fbar p) : LevelCuspCharacters.torVal θ⁻¹ z = LevelCuspCharacters.torVal θ z⁻¹ := by
  have hinj : Function.Injective
      (fun u : LevelCuspCharacters.Tor p d => ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p)) :=
    fun a b hab => Subtype.ext (Units.ext hab)
  unfold LevelCuspCharacters.torVal
  by_cases hz : ∃ u : LevelCuspCharacters.Tor p d, ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) = z
  · obtain ⟨u, rfl⟩ := hz
    have h2 : (((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p))⁻¹ =
        (((u⁻¹ : LevelCuspCharacters.Tor p d) : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) := by simp
    rw [h2, hinj.extend_apply, hinj.extend_apply]
    simp
  · rw [Function.extend_apply' _ _ _ hz, Function.extend_apply']
    · rfl
    · rintro ⟨u, hu⟩
      exact hz ⟨u⁻¹, by simp [hu]⟩

/- English proof (translation)
Introduce `p _ K _ ι _ _ θ h h' hh`. Establish `hh' : h' * h = 1` using `mul_eq_one_comm.1 hh`. Establish `key : ∀ (a b : Matrix ι ι (ZMod p)), a * b = 1 → Matrix.toLin' (a.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) * Matrix.toLin' (b.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) = 1`. Introduce `a b hab`. Rewrite using `[Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hab, Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]`.

Both sides reduce to the same expression. Establish `heig` using `eigenspace_inv _ _ (key h h' hh) (key h' h hh')`. Establish `hmem : ∀ z : LevelCuspCharacters.Fbar p, z ∈ (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset ↔ z⁻¹ ∈ (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset`. Introduce `z`. Rewrite using `[Multiset.mem_toFinset, Multiset.mem_toFinset, mem_aroots_iff, mem_aroots_iff, heig]`.

Establish `hcard : (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card = (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card` using `Finset.card_bijective _ inv_involutive.bijective hmem`. Unfold `LevelCuspCharacters.cuspChar`. Distinguish the cases in `H : ∃ (φ : (ZMod p)[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n`. Rewrite using `[if_pos H, if_pos (powIrr_of_inv h h' hh H)]`. Use `congr 1`.

Use `Finset.sum_bijective _ inv_involutive.bijective (by convert hmem) ?_` and prove the remaining obligations. Introduce `z _`. Rewrite using `[torVal_inv, heig]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Use `congr 3`. Rewrite using `[if_neg H, if_neg (fun H' => H (powIrr_of_inv h' h hh' H'))]`.
-/
theorem cuspChar_inv : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (θ : LevelCuspCharacters.Tor p (Fintype.card ι) →* Kˣ) (h h' : Matrix ι ι (ZMod p)),
    h * h' = 1 → LevelCuspCharacters.cuspChar θ⁻¹ h = LevelCuspCharacters.cuspChar θ h' := by
  intro p _ K _ ι _ _ θ h h' hh
  classical
  have hh' : h' * h = 1 := mul_eq_one_comm.1 hh
  have key : ∀ (a b : Matrix ι ι (ZMod p)), a * b = 1 →
      Matrix.toLin' (a.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) *
        Matrix.toLin' (b.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) = 1 := by
    intro a b hab
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  have heig := eigenspace_inv _ _ (key h h' hh) (key h' h hh')
  have hmem : ∀ z : LevelCuspCharacters.Fbar p, z ∈ (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset ↔
      z⁻¹ ∈ (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset := by
    intro z
    rw [Multiset.mem_toFinset, Multiset.mem_toFinset, mem_aroots_iff, mem_aroots_iff, heig]
  have hcard : (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card =
      (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card :=
    Finset.card_bijective _ inv_involutive.bijective hmem
  unfold LevelCuspCharacters.cuspChar
  by_cases H : ∃ (φ : (ZMod p)[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n
  · rw [if_pos H, if_pos (powIrr_of_inv h h' hh H)]
    congr 1
    refine Finset.sum_bijective _ inv_involutive.bijective (by convert hmem) ?_
    intro z _
    rw [torVal_inv, heig]
    congr 2
    funext i
    congr 3
  · rw [if_neg H, if_neg (fun H' => H (powIrr_of_inv h' h hh' H'))]

end GlobalTheory.CuspInv
