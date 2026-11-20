import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PartnersFactorsOfKernelSmith
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SmithPairing

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Establish `h : (Set.range fun i => (B i : E)) = Λ.subtype '' Set.range B`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h, Submodule.span_image, B.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem span_coe_basis {E : Type} [AddCommGroup E] [Module O E] (Λ : Submodule O E) {n : ℕ}
    (B : Module.Basis (Fin n) O Λ) : Submodule.span O (Set.range fun i => (B i : E)) = Λ := by
  have h : (Set.range fun i => (B i : E)) = Λ.subtype '' Set.range B := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, B.span_eq, Submodule.map_top, Submodule.range_subtype]

/- English proof (translation)
Simplify using `[fock]`.
-/
theorem fock_zero_right {σ : Type} (F : MvPolynomial σ (KK O)) : fock F (0 : MvPolynomial σ (KK O)) = 0 := by
  simp [fock]

/- English proof (translation)
Use `haveI : Module.Free O Λ := Module.free_of_finite_type_torsion_free'`. Set `e` to `Module.finBasis O Λ`. Take `⟨P, Q, hP, hQ, hd⟩` from `Formalism.InvariantFactorPaths.KP.smithPairing O (KK O) (Module.finrank O Λ) (Matrix.of fun a c => fock (e a : MvPolynomial σ (KK O)) (e c : MvPolynomial σ (KK O)))`. Establish `hPt : IsUnit P.transpose.det` using `by rw [Matrix.det_transpose]; exact hP`. Set `alB` to `e.map (Matrix.toLinearEquiv e P.transpose hPt)`.

Set `beB` to `e.map (Matrix.toLinearEquiv e Q hQ)`. Establish `hal : ∀ i, (alB i : MvPolynomial σ (KK O)) = ∑ a, P i a • (e a : MvPolynomial σ (KK O))` using `fun i => by show ((Matrix.toLin e e P.transpose (e i) : Λ) : MvPolynomial σ (KK O)) = _`. Rewrite using `[Matrix.toLin_self]`. Simplify using `[Matrix.transpose_apply]`. Establish `hbe : ∀ l, (beB l : MvPolynomial σ (KK O)) = ∑ c, Q c l • (e c : MvPolynomial σ (KK O))` using `fun l => by show ((Matrix.toLin e e Q (e l) : Λ) : MvPolynomial σ (KK O)) = _`.

Rewrite using `[Matrix.toLin_self]`. Simplify using the standard rewrite rules. Use `⟨_, fun i => (alB i : MvPolynomial σ (KK O)), fun i => (beB i : MvPolynomial σ (KK O)), fun i => ⟨(alB i).2, (beB i).2⟩, fun i l hil => ?_, ?_, span_coe_basis Λ alB, span_coe_basis Λ beB⟩` and prove the remaining obligations. Establish `h` using `hd i l hil show fock (alB i : MvPolynomial σ (KK O)) (beB l : MvPolynomial σ (KK O)) = 0`. Rewrite using `[hal, hbe, fock_bilin]`.

Rewrite `h` using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul] at h`. Rewrite `h` using `[Finset.sum_comm]`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `alB.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)`.
-/
theorem smith_block {σ : Type} (Λ : Submodule O (MvPolynomial σ (KK O))) (hfg : Module.Finite O Λ) :
    ∃ (n : ℕ) (al be : Fin n → MvPolynomial σ (KK O)), (∀ i, al i ∈ Λ ∧ be i ∈ Λ) ∧
      (∀ i l, i ≠ l → fock (al i) (be l) = 0) ∧ LinearIndependent O al ∧
      Submodule.span O (Set.range al) = Λ ∧ Submodule.span O (Set.range be) = Λ := by
  classical
  haveI : Module.Free O Λ := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis O Λ
  obtain ⟨P, Q, hP, hQ, hd⟩ := Formalism.InvariantFactorPaths.KP.smithPairing O (KK O) (Module.finrank O Λ)
    (Matrix.of fun a c => fock (e a : MvPolynomial σ (KK O)) (e c : MvPolynomial σ (KK O)))
  have hPt : IsUnit P.transpose.det := by rw [Matrix.det_transpose]; exact hP
  let alB := e.map (Matrix.toLinearEquiv e P.transpose hPt)
  let beB := e.map (Matrix.toLinearEquiv e Q hQ)
  have hal : ∀ i, (alB i : MvPolynomial σ (KK O)) = ∑ a, P i a • (e a : MvPolynomial σ (KK O)) := fun i => by
    show ((Matrix.toLin e e P.transpose (e i) : Λ) : MvPolynomial σ (KK O)) = _
    rw [Matrix.toLin_self]
    simp [Matrix.transpose_apply]
  have hbe : ∀ l, (beB l : MvPolynomial σ (KK O)) = ∑ c, Q c l • (e c : MvPolynomial σ (KK O)) := fun l => by
    show ((Matrix.toLin e e Q (e l) : Λ) : MvPolynomial σ (KK O)) = _
    rw [Matrix.toLin_self]
    simp
  refine ⟨_, fun i => (alB i : MvPolynomial σ (KK O)), fun i => (beB i : MvPolynomial σ (KK O)),
    fun i => ⟨(alB i).2, (beB i).2⟩, fun i l hil => ?_, ?_, span_coe_basis Λ alB, span_coe_basis Λ beB⟩
  · have h := hd i l hil
    show fock (alB i : MvPolynomial σ (KK O)) (beB l : MvPolynomial σ (KK O)) = 0
    rw [hal, hbe, fock_bilin]
    rw [Matrix.mul_apply] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul] at h
    rw [Finset.sum_comm] at h
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul]
    ring
  · exact alB.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_pi]`. Introduce `i _`.

Use `beta_reduce`. Distinguish the cases in `h : i = x.1.1`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same, ← hspan]`. Conclude with `Submodule.subset_span ⟨x.2, rfl⟩`.

Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `Submodule.zero_mem _`. Introduce `f hf`. Rewrite `hf` using `[Submodule.mem_pi]`. Establish `hfT : f = ∑ b ∈ T, Pi.single b (f b)`.

Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply, Finset.sum_pi_single]`. Use `split_ifs with hi`. Both sides reduce to the same expression. Establish `h0` using `hf i (Set.mem_univ i)`.

Rewrite `h0` using `[hM i hi, Submodule.mem_bot]`. Conclude with `h0`. Rewrite using `[hfT]`. Use `Submodule.sum_mem _ fun b hb => ?_` and prove the remaining obligations. Establish `hfb : f b ∈ Submodule.span O (Set.range (al b))`.

Rewrite using `[hspan]`. Conclude with `hf b (Set.mem_univ b)`. Establish `e : (Pi.single b (f b) : β → E) = LinearMap.single O (fun _ : β => E) b (f b)` using `rfl`. Rewrite using `[e]`. Establish `hmap` using `Submodule.mem_map_of_mem (f := LinearMap.single O (fun _ : β => E) b) hfb`.

Rewrite `hmap` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ hmap` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Conclude with `⟨⟨⟨b, hb⟩, i⟩, rfl⟩`.
-/
theorem span_single {β E : Type} [DecidableEq β] [AddCommGroup E] [Module O E] (M : β → Submodule O E) (T : Finset β)
    (hM : ∀ b, b ∉ T → M b = ⊥) (n : β → ℕ) (al : ∀ b, Fin (n b) → E)
    (hspan : ∀ b, Submodule.span O (Set.range (al b)) = M b) :
    Submodule.span O (Set.range fun x : (Σ b : {b // b ∈ T}, Fin (n b.1)) =>
      (Pi.single x.1.1 (al x.1.1 x.2) : β → E)) = Submodule.pi Set.univ M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_pi]
    intro i _
    beta_reduce
    by_cases h : i = x.1.1
    · subst h
      rw [Pi.single_eq_same, ← hspan]
      exact Submodule.subset_span ⟨x.2, rfl⟩
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  · intro f hf
    rw [Submodule.mem_pi] at hf
    have hfT : f = ∑ b ∈ T, Pi.single b (f b) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_pi_single]
      split_ifs with hi
      · rfl
      · have h0 := hf i (Set.mem_univ i)
        rw [hM i hi, Submodule.mem_bot] at h0
        exact h0
    rw [hfT]
    refine Submodule.sum_mem _ fun b hb => ?_
    have hfb : f b ∈ Submodule.span O (Set.range (al b)) := by
      rw [hspan]
      exact hf b (Set.mem_univ b)
    have e : (Pi.single b (f b) : β → E) = LinearMap.single O (fun _ : β => E) b (f b) := rfl
    rw [e]
    have hmap := Submodule.mem_map_of_mem (f := LinearMap.single O (fun _ : β => E) b) hfb
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨⟨b, hb⟩, i⟩, rfl⟩

end Gen

def BlockFGAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r] (s : ℕ) (S : SegData s)
    (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) (w : O), Irreducible w → w ^ 2 = (p : O) →
    Module.Finite O (blockLat O p r S aTop aPlus m b)

open Classical in

/- English proof (translation)
Establish `hfin` using `kf_kept_finite p r S aTop`. Use `set T := hfin.toFinset with hT`. Establish `hmemT : ∀ b, b ∈ T ↔ Kept p r S aTop b` using `fun b => by rw [hT, Set.Finite.mem_toFinset]; rfl`. Set `M : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O))` to `fun b => if Kept p r S aTop b then blockLat O p r S aTop aPlus m b else ⊥`. Establish `hMfg : ∀ b, Module.Finite O (M b)` using `fun b => by`.

Distinguish the cases in `hb : Kept p r S aTop b`. Establish `e : M b = blockLat O p r S aTop aPlus m b` using `if_pos hb`. Rewrite using `[e]`. Conclude with `hFG b`. Establish `e : M b = ⊥` using `if_neg hb`.

Rewrite using `[e]`. Use `infer_instance`. Establish `hM0 : ∀ b, b ∉ T → M b = ⊥` using `fun b hb => if_neg fun h => hb ((hmemT b).2 h)`. Use `choose n al be hmem horth hli hsa hsb using fun b => smith_block (M b) (hMfg b)`. Set `ι` to `Σ b : {b // b ∈ T}, Fin (n b.1)`.

Set `ev : ι ≃ Fin (Fintype.card ι)` to `Fintype.equivFin ι`. Set `AL : ι → SegVs O r s S.t` to `fun x => Pi.single x.1.1 (al x.1.1 x.2)`. Set `BE : ι → SegVs O r s S.t` to `fun x => Pi.single x.1.1 (be x.1.1 x.2)`. Establish `hL : segLat O p r S aTop aPlus m = Submodule.pi Set.univ M` using `rfl`. Establish `hALs : Submodule.span O (Set.range AL) = Submodule.pi Set.univ M` using `span_single M T hM0 n al hsa`.

Establish `hBEs : Submodule.span O (Set.range BE) = Submodule.pi Set.univ M` using `span_single M T hM0 n be hsb`. Use `⟨Fintype.card ι, AL ∘ ev.symm, BE ∘ ev.symm, fun i => (ev.symm i).1.1, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[hL, ← hALs]`. Use `⟨Submodule.subset_span ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hALs, ← hBEs]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Introduce `i b hb`. Conclude with `⟨Pi.single_eq_of_ne hb _, Pi.single_eq_of_ne hb _⟩`. Introduce `i l hil set x := ev.symm i with hx set y := ev.symm l with hy`.

Establish `hxy : x ≠ y` using `fun h => hil (ev.symm.injective h)`. Use `show segForm O p r S (AL x) (BE y) = 0`. Rewrite using `[segForm_eq_sum p r S {x.1.1} (AL x) (BE y) (fun b hb => Pi.single_eq_of_ne (by simpa using hb) _), Finset.sum_singleton]`. Use `show _ * fock ((Pi.single x.1.1 (al x.1.1 x.2) : SegVs O r s S.t) x.1.1) ((Pi.single y.1.1 (be y.1.1 y.2) : SegVs O r s S.t) x.1.1) = 0`. Rewrite using `[Pi.single_eq_same]`.

Distinguish the cases in `hb : x.1.1 = y.1.1`. Take `⟨⟨xb, hxb⟩, xi⟩` from `x`. Take `⟨⟨yb, hyb⟩, yi⟩` from `y`. Simplify using `only at hb`. Substitute `hb` using the available equality.

Rewrite using `[Pi.single_eq_same, horth xb xi yi (fun h => hxy (by rw [h])), mul_zero]`. Rewrite using `[Pi.single_eq_of_ne hb, fock_zero_right, mul_zero]`. Establish `h1` using `Pi.linearIndependent_single (R := O) al hli`. Establish `hj : Function.Injective (fun x : ι => (⟨x.1.1, x.2⟩ : Σ b, Fin (n b)))`. Introduce and unpack `⟨⟨xb, hxb⟩, xi⟩ ⟨⟨yb, hyb⟩, yi⟩ h`.

Simplify using `only [Sigma.mk.injEq] at h`. Take `⟨h1, h2⟩` from `h`. Substitute `h1` using the available equality. Rewrite using `[eq_of_heq h2]`. Conclude with `(h1.comp _ hj).comp _ ev.symm.injective`.

Rewrite using `[hL, ← hALs, EquivLike.range_comp]`. Rewrite using `[hL, ← hBEs, EquivLike.range_comp]`.
-/
theorem smithData_seg {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r] {s : ℕ}
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ)
    (hFG : ∀ b, Module.Finite O (blockLat O p r S aTop aPlus m b)) :
    ∃ (n : ℕ) (al be : Fin n → SegVs O r s S.t) (β : Fin n → SegBlock s r),
      SmithData (segForm O p r S) (segLat O p r S aTop aPlus m) n al be β := by
  have hfin := kf_kept_finite p r S aTop
  set T := hfin.toFinset with hT
  have hmemT : ∀ b, b ∈ T ↔ Kept p r S aTop b := fun b => by rw [hT, Set.Finite.mem_toFinset]; rfl
  let M : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
    fun b => if Kept p r S aTop b then blockLat O p r S aTop aPlus m b else ⊥
  have hMfg : ∀ b, Module.Finite O (M b) := fun b => by
    by_cases hb : Kept p r S aTop b
    · have e : M b = blockLat O p r S aTop aPlus m b := if_pos hb
      rw [e]; exact hFG b
    · have e : M b = ⊥ := if_neg hb
      rw [e]; infer_instance
  have hM0 : ∀ b, b ∉ T → M b = ⊥ := fun b hb => if_neg fun h => hb ((hmemT b).2 h)
  choose n al be hmem horth hli hsa hsb using fun b => smith_block (M b) (hMfg b)
  let ι := Σ b : {b // b ∈ T}, Fin (n b.1)
  let ev : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let AL : ι → SegVs O r s S.t := fun x => Pi.single x.1.1 (al x.1.1 x.2)
  let BE : ι → SegVs O r s S.t := fun x => Pi.single x.1.1 (be x.1.1 x.2)
  have hL : segLat O p r S aTop aPlus m = Submodule.pi Set.univ M := rfl
  have hALs : Submodule.span O (Set.range AL) = Submodule.pi Set.univ M := span_single M T hM0 n al hsa
  have hBEs : Submodule.span O (Set.range BE) = Submodule.pi Set.univ M := span_single M T hM0 n be hsb
  refine ⟨Fintype.card ι, AL ∘ ev.symm, BE ∘ ev.symm, fun i => (ev.symm i).1.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hL, ← hALs]
    refine ⟨Submodule.subset_span ⟨_, rfl⟩, ?_⟩
    rw [hALs, ← hBEs]
    exact Submodule.subset_span ⟨_, rfl⟩
  · intro i b hb
    exact ⟨Pi.single_eq_of_ne hb _, Pi.single_eq_of_ne hb _⟩
  · intro i l hil
    set x := ev.symm i with hx
    set y := ev.symm l with hy
    have hxy : x ≠ y := fun h => hil (ev.symm.injective h)
    show segForm O p r S (AL x) (BE y) = 0
    rw [segForm_eq_sum p r S {x.1.1} (AL x) (BE y) (fun b hb => Pi.single_eq_of_ne (by simpa using hb) _),
      Finset.sum_singleton]
    show _ * fock ((Pi.single x.1.1 (al x.1.1 x.2) : SegVs O r s S.t) x.1.1)
      ((Pi.single y.1.1 (be y.1.1 y.2) : SegVs O r s S.t) x.1.1) = 0
    rw [Pi.single_eq_same]
    by_cases hb : x.1.1 = y.1.1
    · obtain ⟨⟨xb, hxb⟩, xi⟩ := x
      obtain ⟨⟨yb, hyb⟩, yi⟩ := y
      simp only at hb
      subst hb
      rw [Pi.single_eq_same, horth xb xi yi (fun h => hxy (by rw [h])), mul_zero]
    · rw [Pi.single_eq_of_ne hb, fock_zero_right, mul_zero]
  · have h1 := Pi.linearIndependent_single (R := O) al hli
    have hj : Function.Injective (fun x : ι => (⟨x.1.1, x.2⟩ : Σ b, Fin (n b))) := by
      rintro ⟨⟨xb, hxb⟩, xi⟩ ⟨⟨yb, hyb⟩, yi⟩ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      rw [eq_of_heq h2]
    exact (h1.comp _ hj).comp _ ev.symm.injective
  · rw [hL, ← hALs, EquivLike.range_comp]
  · rw [hL, ← hBEs, EquivLike.range_comp]

end Formalism.MainNotions.ColumnSystems.Pf
