import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGridStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.WeilOver

open GlobalTheory.LatVac GlobalTheory.PlaceDatum GlobalTheory.PlaceModel Formalism.IndefR.Mult

variable {D : D7}

section Coset

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_nsmul, zero_nsmul, finTens_zero]`. Consider the case `succ k ih => rw [succ_nsmul, succ_nsmul, finTens_add, ih]`.
-/
theorem finTens_nsmul {m n : ℕ} (α : Af D.host.F) (k : ℕ) (M : Matrix (Fin m) (Fin n) D.host.E) :
    finTens α (k • M) = k • finTens α M := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, finTens_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, finTens_add, ih]

/- English proof (translation)
Take `⟨s, rfl⟩` from `hA`. Use `choose N hN h using fun x : s => h x (Submodule.subset_span x.2)`. Use `⟨∏ x, N x, Finset.prod_pos fun x _ => hN x, fun x hx => ?_⟩` and prove the remaining obligations. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : s)), mul_nsmul']`. Conclude with `nsmul_mem (h ⟨x, hx⟩) _`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [nsmul_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx => rw [smul_comm]`. Conclude with `B.smul_mem c hx`.
-/
theorem exists_uniform {M : Type} [AddCommGroup M] [Module (𝓞 D.host.E) M] {A : Submodule (𝓞 D.host.E) M} (hA : A.FG)
    (B : Submodule (𝓞 D.host.E) M) (h : ∀ x ∈ A, ∃ k : ℕ, 0 < k ∧ k • x ∈ B) : ∃ k : ℕ, 0 < k ∧ ∀ x ∈ A, k • x ∈ B := by
  classical
  obtain ⟨s, rfl⟩ := hA
  choose N hN h using fun x : s => h x (Submodule.subset_span x.2)
  refine ⟨∏ x, N x, Finset.prod_pos fun x _ => hN x, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : s)), mul_nsmul']
    exact nsmul_mem (h ⟨x, hx⟩) _
  | zero => simp
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact B.smul_mem c hx

/- English proof (translation)
Set `B : Submodule (𝓞 D.host.E) (Matrix (Fin T.rank) (Fin S.rank) D.host.E)` to `{ (latRat S T ΛS ΛT).toAddSubmonoid with smul_mem' := fun c _ hx => smul_mem_latRat c hx }`. Conclude with `exists_uniform (Module.Finite.iff_fg.1 (homLat_fg hS hT.fg)) B fun x _ => GlobalTheory.LatVacFull.latRat_full D S T ΛS ΛT hS hT x`.
-/
theorem exists_hom_le (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ homLat ΛS ΛT, k • x ∈ latRat S T ΛS ΛT := by
  let B : Submodule (𝓞 D.host.E) (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    { (latRat S T ΛS ΛT).toAddSubmonoid with smul_mem' := fun c _ hx => smul_mem_latRat c hx }
  exact exists_uniform (Module.Finite.iff_fg.1 (homLat_fg hS hT.fg)) B fun x _ =>
    GlobalTheory.LatVacFull.latRat_full D S T ΛS ΛT hS hT x

/- English proof (translation)
Take `⟨M, hM, h1⟩` from `exists_den_latRat (S := S) (T := T) hS.fg hT.fg`. Take `⟨N, hN, h2⟩` from `exists_den_fg_pi hS.fg`. Establish `h3 : ∀ y : Fin T.rank → D.host.E, ∃ k : ℕ, 0 < k ∧ k • y ∈ ΛT` using `fun y => by`. Establish `hy : y ∈ Submodule.span D.host.E (ΛT : Set (Fin T.rank → D.host.E))` using `hT.span_eq_top ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨1, one_pos, by rwa [one_nsmul]⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hx⟩` from `hx`. Take `⟨b, hb, hy⟩` from `hy`.

Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[nsmul_add]`. Conclude with `add_mem (by rw [mul_nsmul]; exact nsmul_mem hx _) (by rw [mul_nsmul']; exact nsmul_mem hy _)`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hx⟩` from `hx`.

Take `⟨b, hb, c', hc⟩` from `GlobalTheory.AdIdem.exists_nat_mul_integral _ c`. Use `⟨b * a, Nat.mul_pos hb ha, ?_⟩` and prove the remaining obligations. Use `ΛT.smul_mem c' hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(b * a) • (c * x i) = algebraMap _ D.host.E c' * (a • x i)`.

Rewrite using `[hc, nsmul_eq_mul, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `choose K hK h3 using fun i : Fin T.rank => h3 (Pi.single i 1)`. Use `⟨(∏ i, K i) * (M * N), Nat.mul_pos (Finset.prod_pos fun i _ => hK i) (Nat.mul_pos hM hN), fun x hx y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[pi_eq_sum_univ' (_ *ᵥ y)]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩ : ∑ j, (M * x i j) * (N * y j) ∈ Formalism.UG.intOE D.host.E` from `sum_mem fun j _ => mul_mem (h1 x hx i j) (h2 y hy j)`. Use `ΛT.smul_mem c (nsmul_mem (h3 i) (∏ j ∈ Finset.univ.erase i, K j)) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`.

Use function extensionality and compare the values at `l`. Express the relevant statement in the definitionally equal form `(∑ j, (((∏ j ∈ Finset.univ.erase i, K j) * K i * (M * N)) • x i j) * y j) * (Pi.single i 1 : _ → D.host.E) l = algebraMap _ D.host.E c * ((∏ j ∈ Finset.univ.erase i, K j) • K i • (Pi.single i 1 : _ → D.host.E) l)`. Simplify using `only [hc, nsmul_eq_mul, Nat.cast_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem exists_le_hom (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ latRat S T ΛS ΛT, k • x ∈ homLat ΛS ΛT := by
  classical
  obtain ⟨M, hM, h1⟩ := exists_den_latRat (S := S) (T := T) hS.fg hT.fg
  obtain ⟨N, hN, h2⟩ := exists_den_fg_pi hS.fg
  have h3 : ∀ y : Fin T.rank → D.host.E, ∃ k : ℕ, 0 < k ∧ k • y ∈ ΛT := fun y => by
    have hy : y ∈ Submodule.span D.host.E (ΛT : Set (Fin T.rank → D.host.E)) := hT.span_eq_top ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by rwa [one_nsmul]⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨b, hb, hy⟩ := hy
      refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
      rw [nsmul_add]
      exact add_mem (by rw [mul_nsmul]; exact nsmul_mem hx _) (by rw [mul_nsmul']; exact nsmul_mem hy _)
    | smul c x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨b, hb, c', hc⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral _ c
      refine ⟨b * a, Nat.mul_pos hb ha, ?_⟩
      convert ΛT.smul_mem c' hx using 1
      funext i
      change (b * a) • (c * x i) = algebraMap _ D.host.E c' * (a • x i)
      rw [hc, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
  choose K hK h3 using fun i : Fin T.rank => h3 (Pi.single i 1)
  refine ⟨(∏ i, K i) * (M * N), Nat.mul_pos (Finset.prod_pos fun i _ => hK i) (Nat.mul_pos hM hN), fun x hx y hy => ?_⟩
  rw [pi_eq_sum_univ' (_ *ᵥ y)]
  refine sum_mem fun i _ => ?_
  obtain ⟨c, hc⟩ : ∑ j, (M * x i j) * (N * y j) ∈ Formalism.UG.intOE D.host.E :=
    sum_mem fun j _ => mul_mem (h1 x hx i j) (h2 y hy j)
  convert ΛT.smul_mem c (nsmul_mem (h3 i) (∏ j ∈ Finset.univ.erase i, K j)) using 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  funext l
  change (∑ j, (((∏ j ∈ Finset.univ.erase i, K j) * K i * (M * N)) • x i j) * y j) * (Pi.single i 1 : _ → D.host.E) l =
    algebraMap _ D.host.E c * ((∏ j ∈ Finset.univ.erase i, K j) • K i • (Pi.single i 1 : _ → D.host.E) l)
  simp only [hc, nsmul_eq_mul, Nat.cast_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Take `⟨a, ha, h1⟩` from `exists_hom_le hS hT`. Take `⟨b, hb, h2⟩` from `exists_le_hom hS hT`. Establish `hN : 0 < Ideal.absNorm 𝔪` using `Nat.pos_of_ne_zero fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `k1 : ∀ u ∈ latO S T ΛS ΛT fun _ => True, (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT)` using `fun u hu => by`. Use `latO_induction (p := fun u => (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT)) ?_ ?_ ?_ ?_ hu` and prove the remaining obligations.

Introduce `α hα X hX`. Rewrite using `[← finTens_nsmul]`. Use `AddSubgroup.subset_closure ⟨α, hα, _, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[mul_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]`. Conclude with `Submodule.smul_mem_smul (Ideal.absNorm_mem _) (h2 X hX)`.

Rewrite using `[nsmul_zero]`. Conclude with `zero_mem _`. Introduce `x y hx hy`. Rewrite using `[nsmul_add]`. Conclude with `add_mem hx hy`.

Introduce `x hx`. Rewrite using `[neg_nsmul]`. Conclude with `neg_mem hx`. Establish `k2 : ∀ u ∈ hatMx (𝔪 • homLat ΛS ΛT), a • u ∈ latO S T ΛS ΛT fun _ => True` using `fun u hu => by`. Proceed by induction on `hu using AddSubgroup.closure_induction with`.

Consider the case `mem w hw`. Take `⟨α, hα, x, hx, rfl⟩` from `hw`. Conclude with `finTens_nsmul α a x ▸ finTens_mem_latO hα (h1 x (Submodule.smul_le_right hx))`. Consider the case `zero => rw [nsmul_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [nsmul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [neg_nsmul]`. Conclude with `neg_mem hx`. Establish `hsupp : ∀ t, cosInd e κ t ≠ 0 → t ∈ cosSet e κ` using `fun t ht => Set.mem_of_indicator_ne_zero ht`.

Use `⟨fun t ht => (hsupp t ht).1, a * (b * Ideal.absNorm 𝔪), by positivity, fun u hu hh t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hk : (a * (b * Ideal.absNorm 𝔪)) • u ∈ hatMx (𝔪 • homLat ΛS ΛT)`. Rewrite using `[mul_nsmul']`. Conclude with `nsmul_mem (k1 u hu) _`. Establish `hi : t + (a * (b * Ideal.absNorm 𝔪)) • u ∈ cosSet e κ ↔ t ∈ cosSet e κ`.

Use `and_congr ?_ (exists_congr fun x => and_congr_right fun _ => ?_)` and prove the remaining obligations. Rewrite using `[isHalf_iff S T, isHalf_iff S T]`. Conclude with `AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((isHalf_iff S T).1 hh) _)`. Rewrite using `[add_sub_right_comm]`. Conclude with `AddSubgroup.add_mem_cancel_right _ hk`.

Distinguish the cases in `ht : t ∈ cosSet e κ`. Conclude with `(Set.indicator_of_mem (hi.2 ht) _).trans (Set.indicator_of_mem ht (1 : WO S T → ℂ)).symm`. Conclude with `(Set.indicator_of_notMem (fun h => ht (hi.1 h)) _).trans (Set.indicator_of_notMem ht _).symm`. Take `⟨-, x, -, hx⟩` from `hsupp t ht`. Rewrite using `[mul_nsmul]`.

Use `nsmul_mem ?_ _` and prove the remaining obligations. Establish `e1 : e • (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E).map (incA D) = e • finTens 1 x.1`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `e * incA D (x.1 i j) = e * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] x.1 i j)`. Use `conv_lhs => rw [← mul_pair_one hinf, mul_assoc]`.

Use `congr 1`. Conclude with `(Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).trans (by rw [mul_one, one_mul])`. Establish `e2` using `GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])) _ (finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (h1 x.1 x.2))`. Establish `e3` using `add_mem (k2 _ hx) e2`. Rewrite `e3` using `[finTens_nsmul, e1, smul_comm e a, ← nsmul_add, sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem isSBHalf_cosInd (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) {e : AE D}
    (he : e * e = e) (hinf : infPart D e = 0) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (κ : Cos ΛS ΛT 𝔪) :
    IsSBHalf e (latO S T ΛS ΛT fun _ => True) (cosInd e κ) := by
  obtain ⟨a, ha, h1⟩ := exists_hom_le hS hT
  obtain ⟨b, hb, h2⟩ := exists_le_hom hS hT
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)
  have k1 : ∀ u ∈ latO S T ΛS ΛT fun _ => True, (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT) := fun u hu => by
    refine latO_induction (p := fun u => (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT)) ?_ ?_ ?_ ?_ hu
    · intro α hα X hX
      rw [← finTens_nsmul]
      refine AddSubgroup.subset_closure ⟨α, hα, _, ?_, rfl⟩
      rw [mul_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]
      exact Submodule.smul_mem_smul (Ideal.absNorm_mem _) (h2 X hX)
    · rw [nsmul_zero]; exact zero_mem _
    · intro x y hx hy; rw [nsmul_add]; exact add_mem hx hy
    · intro x hx; rw [neg_nsmul]; exact neg_mem hx
  have k2 : ∀ u ∈ hatMx (𝔪 • homLat ΛS ΛT), a • u ∈ latO S T ΛS ΛT fun _ => True := fun u hu => by
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hw
      exact finTens_nsmul α a x ▸ finTens_mem_latO hα (h1 x (Submodule.smul_le_right hx))
    | zero => rw [nsmul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
    | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx
  have hsupp : ∀ t, cosInd e κ t ≠ 0 → t ∈ cosSet e κ := fun t ht => Set.mem_of_indicator_ne_zero ht
  refine ⟨fun t ht => (hsupp t ht).1, a * (b * Ideal.absNorm 𝔪), by positivity, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have hk : (a * (b * Ideal.absNorm 𝔪)) • u ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
      rw [mul_nsmul']; exact nsmul_mem (k1 u hu) _
    have hi : t + (a * (b * Ideal.absNorm 𝔪)) • u ∈ cosSet e κ ↔ t ∈ cosSet e κ := by
      refine and_congr ?_ (exists_congr fun x => and_congr_right fun _ => ?_)
      · rw [isHalf_iff S T, isHalf_iff S T]
        exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((isHalf_iff S T).1 hh) _)
      · rw [add_sub_right_comm]
        exact AddSubgroup.add_mem_cancel_right _ hk
    by_cases ht : t ∈ cosSet e κ
    · exact (Set.indicator_of_mem (hi.2 ht) _).trans (Set.indicator_of_mem ht (1 : WO S T → ℂ)).symm
    · exact (Set.indicator_of_notMem (fun h => ht (hi.1 h)) _).trans (Set.indicator_of_notMem ht _).symm
  · obtain ⟨-, x, -, hx⟩ := hsupp t ht
    rw [mul_nsmul]
    refine nsmul_mem ?_ _
    have e1 : e • (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E).map (incA D) = e • finTens 1 x.1 := by
      ext i j
      change e * incA D (x.1 i j) = e * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] x.1 i j)
      conv_lhs => rw [← mul_pair_one hinf, mul_assoc]
      congr 1
      exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).trans (by rw [mul_one, one_mul])
    have e2 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])) _
      (finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (h1 x.1 x.2))
    have e3 := add_mem (k2 _ hx) e2
    rwa [finTens_nsmul, e1, smul_comm e a, ← nsmul_add, sub_add_cancel] at e3

end Coset

/- English proof (translation)
Establish `hu` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `e1` using `Matrix.mul_nonsing_inv _ hu`. Establish `e2` using `Matrix.nonsing_inv_mul _ hu`. Establish `hs : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1`. Rewrite using `[Formalism.REAL.Jm, diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hs' : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ)`. Rewrite using `[Formalism.REAL.Jm, diagonal_conjTranspose]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[Pi.star_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[← M.fr_gram τ, cart, onb]`.

Generalize the expression as in `(M.fr τ)⁻¹ = B at e1 e2`. Generalize the expression as in `M.fr τ = A at e1 e2`. Establish `e3 : Bᴴ * Aᴴ = 1` using `by rw [← conjTranspose_mul, e1, conjTranspose_one]`. Use `⟨?_, M.ε τ, ?_, by rw [Matrix.mul_assoc, e1, Matrix.mul_one]⟩` and prove the remaining obligations. Generalize the expression as in `Formalism.REAL.Jm (M.ε τ) = s at hs hs'`.

Establish `hGs : Aᴴ * s * A * (B * s * A) = Aᴴ * A`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, hGs, conjTranspose_mul, conjTranspose_mul, hs']`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hGs]`. Conclude with `Matrix.PosDef.conjTranspose_mul_self A (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse e2)))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem model_spec {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) ∧ ∃ ε : Fin V.rank → Bool,
      (onb M τ)ᴴ * gramAt D V τ * onb M τ = Formalism.REAL.Jm ε ∧ cart M τ * onb M τ = onb M τ * Formalism.REAL.Jm ε := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have e1 := Matrix.mul_nonsing_inv _ hu
  have e2 := Matrix.nonsing_inv_mul _ hu
  have hs : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    rw [Formalism.REAL.Jm, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hs' : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    rw [Formalism.REAL.Jm, diagonal_conjTranspose]
    congr 1
    funext a
    rw [Pi.star_apply]
    split_ifs <;> simp
  rw [← M.fr_gram τ, cart, onb]
  generalize (M.fr τ)⁻¹ = B at e1 e2
  generalize M.fr τ = A at e1 e2
  have e3 : Bᴴ * Aᴴ = 1 := by rw [← conjTranspose_mul, e1, conjTranspose_one]
  refine ⟨?_, M.ε τ, ?_, by rw [Matrix.mul_assoc, e1, Matrix.mul_one]⟩
  · generalize Formalism.REAL.Jm (M.ε τ) = s at hs hs'
    have hGs : Aᴴ * s * A * (B * s * A) = Aᴴ * A := by
      calc _ = Aᴴ * (s * (A * B) * s) * A := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [e1, Matrix.mul_one, hs, Matrix.mul_one]
    refine ⟨?_, ?_, ?_⟩
    · calc _ = B * (s * (A * B) * s) * A := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [e1, Matrix.mul_one, hs, Matrix.mul_one, e2]
    · rw [Matrix.mul_assoc, hGs, conjTranspose_mul, conjTranspose_mul, hs']
      calc _ = Aᴴ * (s * (Bᴴ * Aᴴ)) * A := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [e3, Matrix.mul_one]
    · rw [hGs]
      exact Matrix.PosDef.conjTranspose_mul_self A
        (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2
          (Matrix.isUnit_det_of_left_inverse e2)))
  · calc _ = (Bᴴ * Aᴴ) * Formalism.REAL.Jm (M.ε τ) * (A * B) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e1, e3, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Introduce `τ` and use `by have e : (negSp V).gram.map τ = -(V.gram.map τ) := Matrix.ext fun i j => map_neg τ _ rw [e] exact GlobalTheory.Grid.hasSignature_neg (h τ)`.
-/
theorem sigOK_negSp {V : HSp D} (h : V.SigOK) : (negSp V).SigOK := fun τ => by
  have e : (negSp V).gram.map τ = -(V.gram.map τ) := Matrix.ext fun i j => map_neg τ _
  rw [e]
  exact GlobalTheory.Grid.hasSignature_neg (h τ)

def IsMaj (V : HSp D) (s B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, IsCartanInv (gramAt D V τ) (s τ) ∧ ∃ ε : Fin V.rank → Bool,
    (B τ)ᴴ * gramAt D V τ * B τ = Formalism.REAL.Jm ε ∧ s τ * B τ = B τ * Formalism.REAL.Jm ε

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨_, _, model_spec M, HEq.rfl, HEq.rfl⟩`.
-/
theorem exists_maj_heq {V V' : HSp D} (h : V' = V) {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    ∃ s B, IsMaj V' s B ∧ HEq s (cart M) ∧ HEq B (onb M) := by
  subst h
  exact ⟨_, _, model_spec M, HEq.rfl, HEq.rfl⟩

/- English proof (translation)
Substitute `h h'` using the available equality. Conclude with `⟨ω, hω, HEq.rfl⟩`.
-/
theorem exists_om_heq {S S' T T' : HSp D} (h : S' = S) (h' : T' = T) {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT ω) :
    ∃ ω', IsWeilDatumO ψ S' T' χS χT ω' ∧ HEq ω' ω := by
  subst h h'
  exact ⟨ω, hω, HEq.rfl⟩

/- English proof (translation)
Take `⟨f, hf⟩` from `GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ S T sS sT kS kT cS cT ΛS ΛT dS dT`. Use `choose c hc using fun κ : Cos ΛS ΛT 𝔪 => exists_isThetaAt hψ dS dT (idemSum_mul_self he) (infPart_idemSum he) (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ S T ΛS ΛT dS dT P e he f hf.2.theta hf.2.lat).1 (isSBHalf_cosInd dS.1 dT.1 (idemSum_mul_self he) (infPart_idemSum h …`. Conclude with `⟨f, c, hf, hc⟩`.
-/
theorem exists_vac_cos {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (kS : S.SigOK) (kT : T.SigOK)
    (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ (f : WO S T → ℂ) (c : Cos ΛS ΛT 𝔪 → WO S T → ℂ), IsVacO ψ θ S T sS sT ΛS ΛT f ∧
      ∀ κ, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f (cosInd e κ) (c κ) := by
  obtain ⟨f, hf⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ S T sS sT kS kT cS cT ΛS ΛT dS dT
  choose c hc using fun κ : Cos ΛS ΛT 𝔪 => exists_isThetaAt hψ dS dT (idemSum_mul_self he) (infPart_idemSum he)
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ S T ΛS ΛT dS dT P e he f hf.2.theta hf.2.lat).1
    (isSBHalf_cosInd dS.1 dT.1 (idemSum_mul_self he) (infPart_idemSum he) h𝔪 κ)
  exact ⟨f, c, hf, hc⟩

/- English proof (translation)
Establish `h1 : ∀ i, ∃ (f : WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ) (c : G.CosAt i → WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ), i < D.R.m → IsVacO ψ θ _ _ (G.cartS s (.chi i 0)) (G.onT s (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) f ∧ ∀ κ : G.CosAt i, IsThetaAt …` using `fun i => by`. Distinguish the cases in `hi : i < D.R.m`. Use `swap`. Conclude with `⟨0, 0, fun h => absurd h hi⟩`. Take `⟨f, c, h⟩` from `exists_vac_cos hψ hθ (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0)) (sS := G.cartS s (.chi i 0)) (sT := G.onT s (.chi i 0)) (sigOK_negSp (hV (i + 1) hi).1) (hV i hi.le).1 (fun τ => isCartanInv_neg (hs (.grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩ τ).1) (fun τ => (hs (.grid i 0) ⟨hi.le, Na …`.

Conclude with `⟨f, c, fun _ => h⟩`. Use `choose f c h using h1`. Conclude with `⟨⟨ψ, hψ, θ, hθ, s, fun X hX τ => (hs X hX τ).1, B, fun X hX τ => (hs X hX τ).2, om, hom, f, fun i hi => (h i hi).1, c, e, he, fun i hi => (h i hi).2⟩, rfl, rfl, rfl, rfl, rfl⟩`.
-/
theorem exists_weil {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)
    (hV : ∀ i, i ≤ D.R.m → (G.V (.grid i 0)).SigOK ∧ IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)))
    {e : AE D} (he : IsIdemSum e G.pl.W0) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) (s B : ∀ X : Node, D.what₂.Tau → Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ)
    (hs : ∀ X : Node, X.InRange D.R.m → IsMaj (G.V X) (s X) (B X))
    (om : ∀ p : Pair T, GA D (G.pS p) × GA D (G.pT p) →* Module.End ℂ (WO (G.pS p) (G.pT p) → ℂ))
    (hom : ∀ p : Pair T, p.InRange D.R.m → IsWeilDatumO ψ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) (om p)) :
    ∃ W : G.Weil, W.ψ = ψ ∧ W.θ = θ ∧ W.cart = s ∧ W.onb = B ∧ W.om = om := by
  have h1 : ∀ i, ∃ (f : WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ)
      (c : G.CosAt i → WO (G.pS (.chi i 0)) (G.pT (.chi i 0)) → ℂ), i < D.R.m →
      IsVacO ψ θ _ _ (G.cartS s (.chi i 0)) (G.onT s (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) f ∧
      ∀ κ : G.CosAt i, IsThetaAt ψ (symplO _ _) (heisO ψ _ _) e
        (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1
        f (cosInd e κ) (c κ) := fun i => by
    by_cases hi : i < D.R.m
    swap
    · exact ⟨0, 0, fun h => absurd h hi⟩
    obtain ⟨f, c, h⟩ := exists_vac_cos hψ hθ (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0))
      (sS := G.cartS s (.chi i 0)) (sT := G.onT s (.chi i 0)) (sigOK_negSp (hV (i + 1) hi).1) (hV i hi.le).1
      (fun τ => isCartanInv_neg (hs (.grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩ τ).1)
      (fun τ => (hs (.grid i 0) ⟨hi.le, Nat.zero_le _⟩ τ).1) (ΛS := G.latS (.chi i 0)) (ΛT := G.latT (.chi i 0))
      (isSelfDualC_neg (hV (i + 1) hi).2) (hV i hi.le).2 he (G.pl.modul_ne_bot sc)
    exact ⟨f, c, fun _ => h⟩
  choose f c h using h1
  exact ⟨⟨ψ, hψ, θ, hθ, s, fun X hX τ => (hs X hX τ).1, B, fun X hX τ => (hs X hX τ).2, om, hom, f,
    fun i hi => (h i hi).1, c, e, he, fun i hi => (h i hi).2⟩, rfl, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ChiGrid.WeilOver

end
