import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselDecomp

open GlobalTheory.BesselCompare (hA_add hA_smul hA_sum hA_vec hD_swap_zero)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

/- English proof (translation)
Establish `hz : star (B.hT d.z d.z) = B.hT d.z d.z` using `(hT_swap rfl).symm`. Establish `zz : B.hT d.z d.z ≠ 0` using `d.zz`. Unfold `BesselDatum.aux dual`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun j => ?_) i <;> refine Fin.lastCases ?_ (fun k => ?_) l`. Simplify using `[HSpace.hD, starRingEnd_apply, hz, zz]`.

Establish `: B.hT d.z (d.e k) = 0` using `d.ez k`. Simplify using `[HSpace.hD, this, Fin.castSucc_ne_last]`. Rewrite using `[Fin.snoc_last, Fin.snoc_castSucc, hD_swap_zero (d.fz j), if_neg (Fin.castSucc_ne_last j).symm]`. Rewrite using `[Fin.snoc_castSucc, Fin.snoc_castSucc, d.ef]`. Simplify using the standard rewrite rules.
-/
theorem hD_basis_dual (d : BesselDatum A B ι) (i l) : B.hD (d.aux l) (dual d i) = if l = i then 1 else 0 := by
  have hz : star (B.hT d.z d.z) = B.hT d.z d.z := (hT_swap rfl).symm
  have zz : B.hT d.z d.z ≠ 0 := d.zz
  unfold BesselDatum.aux dual
  refine Fin.lastCases ?_ (fun j => ?_) i <;> refine Fin.lastCases ?_ (fun k => ?_) l
  · simp [HSpace.hD, starRingEnd_apply, hz, zz]
  · have : B.hT d.z (d.e k) = 0 := d.ez k
    simp [HSpace.hD, this, Fin.castSucc_ne_last]
  · rw [Fin.snoc_last, Fin.snoc_castSucc, hD_swap_zero (d.fz j), if_neg (Fin.castSucc_ne_last j).symm]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, d.ef]
    simp

/- English proof (translation)
Unfold `dual`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Establish `: B.hT d.z (d.f l) = 0` using `d.fz l`. Simplify using `[HSpace.hD, this]`. Rewrite using `[Fin.snoc_castSucc, d.ff]`.
-/
theorem f_dual (d : BesselDatum A B ι) (i l) : B.hD (d.f l) (dual d i) = 0 := by
  unfold dual
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have : B.hT d.z (d.f l) = 0 := d.fz l
    simp [HSpace.hD, this]
  · rw [Fin.snoc_castSucc, d.ff]

/- English proof (translation)
Unfold `BesselDatum.aux`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.snoc_last, hD_swap_zero (d.ez l)]`. Rewrite using `[Fin.snoc_castSucc, d.ee]`.
-/
theorem hD_basis_e (d : BesselDatum A B ι) (i l) : B.hD (d.aux i) (d.e l) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, hD_swap_zero (d.ez l)]
  · rw [Fin.snoc_castSucc, d.ee]

/- English proof (translation)
Establish `h : B.hT (d.e l) (d.f k) = star (if l = k then 1 else 0)` using `hT_swap (d.ef l k)`. Unfold `HSpace.hD`. Rewrite using `[h]`. Distinguish the cases in `e : k = l`. Simplify using `[e]`.

Simplify using `[e, Ne.symm e]`.
-/
theorem f_e (d : BesselDatum A B ι) (k l) : B.hD (d.f k) (d.e l) = if k = l then 1 else 0 := by
  have h : B.hT (d.e l) (d.f k) = star (if l = k then 1 else 0) := hT_swap (d.ef l k)
  unfold HSpace.hD
  rw [h]
  by_cases e : k = l
  · simp [e]
  · simp [e, Ne.symm e]

def comb (d : BesselDatum A B ι) :
    (A.V × (Fin (d.ρ + 1) → D.host.E) × (Fin d.ρ → D.host.E)) →ₗ[D.host.E] B.V :=
  ι.coprod ((Fintype.linearCombination D.host.E d.aux).coprod (Fintype.linearCombination D.host.E d.f))

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 ?_` and prove the remaining obligations. Introduce and unpack `⟨a, s, r⟩ h`. Simplify using `only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h`. Establish `h1 : ∀ i l, B.hT (dual d i) (d.aux l) = if l = i then 1 else 0` using `hD_basis_dual d`. Establish `h2 : ∀ i l, B.hT (dual d i) (d.f l) = 0` using `f_dual d`.

Establish `h3 : ∀ i l, B.hT (d.e l) (d.aux i) = 0` using `hD_basis_e d`. Establish `h4 : ∀ k l, B.hT (d.e l) (d.f k) = if k = l then 1 else 0` using `f_e d`. Establish `h5 : ∀ i, B.hT (dual d i) (ι a) = 0` using `fun i => hD_swap_zero (dual_perp d i a)`. Establish `h6 : ∀ l, B.hT (d.e l) (ι a) = 0` using `fun l => hD_swap_zero (d.eA l a)`. Establish `hs : s = 0`.

Use function extensionality and compare the values at `i`. Simplify `congrArg (B.hT (dual d i)) h` using `[map_sum, h1, h2, h5]`. Establish `hr : r = 0`. Use function extensionality and compare the values at `l`. Simplify `congrArg (B.hT (d.e l)) h` using `[map_sum, h3, h4, h6]`.

Substitute `hs hr` using the available equality. Establish `ha : ι a = 0` using `by simpa using h`. Establish `: a = 0`. Use `A.nondeg.1 a fun y => ?_` and prove the remaining obligations. Rewrite using `[← d.isom a y, ha]`.

Simplify using the standard rewrite rules. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem comb_inj (d : BesselDatum A B ι) : Function.Injective (comb d) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨a, s, r⟩ h
  simp only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h
  have h1 : ∀ i l, B.hT (dual d i) (d.aux l) = if l = i then 1 else 0 := hD_basis_dual d
  have h2 : ∀ i l, B.hT (dual d i) (d.f l) = 0 := f_dual d
  have h3 : ∀ i l, B.hT (d.e l) (d.aux i) = 0 := hD_basis_e d
  have h4 : ∀ k l, B.hT (d.e l) (d.f k) = if k = l then 1 else 0 := f_e d
  have h5 : ∀ i, B.hT (dual d i) (ι a) = 0 := fun i => hD_swap_zero (dual_perp d i a)
  have h6 : ∀ l, B.hT (d.e l) (ι a) = 0 := fun l => hD_swap_zero (d.eA l a)
  have hs : s = 0 := by
    funext i
    simpa [map_sum, h1, h2, h5] using congrArg (B.hT (dual d i)) h
  have hr : r = 0 := by
    funext l
    simpa [map_sum, h3, h4, h6] using congrArg (B.hT (d.e l)) h
  subst hs hr
  have ha : ι a = 0 := by simpa using h
  have : a = 0 := by
    refine A.nondeg.1 a fun y => ?_
    rw [← d.isom a y, ha]; simp
  subst this
  rfl

/- English proof (translation)
Use `Module.Finite.of_basis A.frame` as an intermediate fact. Use `Module.Finite.of_basis B.frame` as an intermediate fact. Use `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 (comb_inj d)` and prove the remaining obligations. Rewrite using `[Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, A.rank_eq, B.rank_eq, d.rank_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem comb_surj (d : BesselDatum A B ι) : Function.Surjective (comb d) := by
  have := Module.Finite.of_basis A.frame
  have := Module.Finite.of_basis B.frame
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 (comb_inj d)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, A.rank_eq, B.rank_eq,
    d.rank_eq]
  omega

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[vecA]`.
-/
theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[vecA, map_sum, Finset.sum_apply]`.
-/
theorem vecA_sum {n : ℕ} (c : Fin n → D.host.E) (v : Fin n → B.V) :
    vecA B (∑ i, c i • v i) = ∑ i, incA D (c i) • vecA B (v i) := by
  funext k; simp [vecA, map_sum, Finset.sum_apply]

/- English proof (translation)
Rewrite using `[iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]`. Use `conv_lhs => rw [← A.frame.sum_repr a, map_sum]`. Simplify using `only [map_smul]`. Rewrite using `[vecA_sum]`. Both sides reduce to the same expression.
-/
theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]
  conv_lhs => rw [← A.frame.sum_repr a, map_sum]
  simp only [map_smul]
  rw [vecA_sum]
  rfl

/- English proof (translation)
Establish `hx : x = ∑ k, x k • vecA B (B.frame k)`. Use function extensionality and compare the values at `j`. Simplify using `[vecA, Finset.sum_apply, Finsupp.single_apply, apply_ite (incA D)]`. Rewrite using `[hx]`. Use `Finset.sum_induction _ (fun y => ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D), y = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l)) ?_ ?_ ?_` and prove the remaining obligations.

Introduce and unpack `_ _ ⟨t, s, r, rfl⟩ ⟨t', s', r', rfl⟩`. Use `⟨t + t', s + s', r + r', ?_⟩` and prove the remaining obligations. Simplify using `only [iA_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws. Conclude with `⟨0, 0, 0, by simp [iA]⟩`.

Introduce `k _`. Take `⟨⟨a, s, r⟩, h⟩` from `comb_surj d (B.frame k)`. Simplify using `only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h`. Use `⟨x k • vecA A a, fun i => x k * incA D (s i), fun l => x k * incA D (r l), ?_⟩` and prove the remaining obligations. Rewrite using `[← h, vecA_add, vecA_add, vecA_sum, vecA_sum, vecA_iota, iA_smul]`.

Simplify using `only [smul_add, Finset.smul_sum, smul_smul, add_assoc]`.
-/
theorem exists_comb (d : BesselDatum A B ι) (x : Fin B.rank → AE D) :
    ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D),
      x = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l) := by
  have hx : x = ∑ k, x k • vecA B (B.frame k) := by
    funext j
    simp [vecA, Finset.sum_apply, Finsupp.single_apply, apply_ite (incA D)]
  rw [hx]
  refine Finset.sum_induction _ (fun y => ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D),
      y = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l)) ?_ ?_ ?_
  · rintro _ _ ⟨t, s, r, rfl⟩ ⟨t', s', r', rfl⟩
    refine ⟨t + t', s + s', r + r', ?_⟩
    simp only [iA_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  · exact ⟨0, 0, 0, by simp [iA]⟩
  · intro k _
    obtain ⟨⟨a, s, r⟩, h⟩ := comb_surj d (B.frame k)
    simp only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h
    refine ⟨x k • vecA A a, fun i => x k * incA D (s i), fun l => x k * incA D (r l), ?_⟩
    rw [← h, vecA_add, vecA_add, vecA_sum, vecA_sum, vecA_iota, iA_smul]
    simp only [smul_add, Finset.smul_sum, smul_smul, add_assoc]

/- English proof (translation)
Rewrite using `[← hA_herm, hA_vec_iA h, map_zero]`.
-/
theorem iA_vec {v : B.V} (h : ∀ x, B.hD v (ι x) = 0) (t : Fin A.rank → AE D) : hA B (iA ι t) (vecA B v) = 0 := by
  rw [← hA_herm, hA_vec_iA h, map_zero]

/- English proof (translation)
Introduce `D A B ι d`. Use `⟨hD_basis_dual d, f_dual d, fun x => ?_⟩` and prove the remaining obligations. Take `⟨t, s, r, h⟩` from `exists_comb d x`. Establish `hs : ∀ i, hA B x (vecA B (dual d i)) = s i` using `fun i => by`. Rewrite using `[h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (dual_perp d i)]`.

Simplify using `[hA_smul, hA_vec, hD_basis_dual, f_dual, apply_ite (incA D)]`. Establish `hr : ∀ l, hA B x (vecA B (d.e l)) = r l` using `fun l => by`. Rewrite using `[h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (d.eA l)]`. Simplify using `[hA_smul, hA_vec, hD_basis_e, f_e, apply_ite (incA D)]`. Conclude with `⟨t, by simp only [hs, hr]; exact h⟩`.
-/
theorem decomp : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι),
    (∀ i l, B.hD (d.aux l) (dual d i) = if l = i then 1 else 0) ∧ (∀ i l, B.hD (d.f l) (dual d i) = 0) ∧
    ∀ x : Fin B.rank → AE D, ∃ t, x = iA ι t + ∑ i, hA B x (vecA B (dual d i)) • vecA B (d.aux i) +
      ∑ l, hA B x (vecA B (d.e l)) • vecA B (d.f l) := by
  intro D A B ι d
  refine ⟨hD_basis_dual d, f_dual d, fun x => ?_⟩
  obtain ⟨t, s, r, h⟩ := exists_comb d x
  have hs : ∀ i, hA B x (vecA B (dual d i)) = s i := fun i => by
    rw [h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (dual_perp d i)]
    simp [hA_smul, hA_vec, hD_basis_dual, f_dual, apply_ite (incA D)]
  have hr : ∀ l, hA B x (vecA B (d.e l)) = r l := fun l => by
    rw [h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (d.eA l)]
    simp [hA_smul, hA_vec, hD_basis_e, f_e, apply_ite (incA D)]
  exact ⟨t, by simp only [hs, hr]; exact h⟩

end GlobalTheory.BesselDecomp

end
