import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableBound
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EvensBeforePairwise
import Formalism.SharpRestriction.GrowthBounds.PathWeight.DvDegOtherMono

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Hom

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
The claim follows from `(dv_pol_iff _ _).2 (IsWeightedHomogeneous.prod s f e fun a ha => (dv_pol_iff _ _).1 (h a ha))`.
-/
theorem pol_prod {α : Type} (s : Finset α) (f : α → MvPolynomial (ι × Fin n) R) (e : α → ι → ℕ)
    (h : ∀ a ∈ s, f a ∈ Pol R n (e a)) : ∏ a ∈ s, f a ∈ Pol R n (∑ a ∈ s, e a) :=
  (dv_pol_iff _ _).2 (IsWeightedHomogeneous.prod s f e fun a ha => (dv_pol_iff _ _).1 (h a ha))

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `Submodule.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Establish `h1 : ∏ i : Fin r, M (σ i) i ∈ Pol R n (∑ i : Fin r, e (σ i))` using `pol_prod Finset.univ _ _ fun i _ => h (σ i) i`. Establish `h2 : (∑ i : Fin r, e (σ i)) = ∑ l, e l` using `Equiv.sum_comp σ e`. Rewrite `h1` using `[h2]`.

Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs` into its components or cases. Rewrite using `[hs, one_smul]`. Conclude with `h1`. Rewrite using `[hs, Units.neg_smul, one_smul]`. Conclude with `Submodule.neg_mem _ h1`.
-/
theorem pol_det {r : ℕ} (M : Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin n) R)) (e : Fin r → ι → ℕ)
    (h : ∀ l b, M l b ∈ Pol R n (e l)) : M.det ∈ Pol R n (∑ l, e l) := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have h1 : ∏ i : Fin r, M (σ i) i ∈ Pol R n (∑ i : Fin r, e (σ i)) :=
    pol_prod Finset.univ _ _ fun i _ => h (σ i) i
  have h2 : (∑ i : Fin r, e (σ i)) = ∑ l, e l := Equiv.sum_comp σ e
  rw [h2] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact h1
  · rw [hs, Units.neg_smul, one_smul]; exact Submodule.neg_mem _ h1

end Hom

section SP

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O]
variable {r k : ℕ} (F : Frames n' r)

/- English proof (translation)
Unfold `xg`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Rewrite using `[dv_pol_iff]`. Establish `h1` using `isWeightedHomogeneous_X (KK O) (letterWeight (ι := Fin n') (n := k)) (posOf n' a, c)`. Establish `h2` using `isWeightedHomogeneous_C (letterWeight (ι := Fin n') (n := k)) (sigMat p n' O g a c b)`.

Use `h1.mul h2` as an intermediate fact. Rewrite `this` using `[add_zero]`. Establish `e : (letterWeight (ι` using `Fin n') (n := k) (posOf n' a, c)) = (Pi.single (posOf n' a) 1 : Fin n' → ℕ) := by`. Use function extensionality and compare the values at `i`. Unfold `letterWeight`.

Simplify using `only [Pi.single_apply]`. Reduce the equality to equality of the corresponding arguments. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem xg_hom (g : Matrix (Fin k) (Fin k) (WF p n')) (a : ℤ) (b : Fin k) :
    xg p n' O n' g a b ∈ Pol (KK O) k (Pi.single (posOf n' a) 1 : Fin n' → ℕ) := by
  unfold xg
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [dv_pol_iff]
  have h1 := isWeightedHomogeneous_X (KK O) (letterWeight (ι := Fin n') (n := k)) (posOf n' a, c)
  have h2 := isWeightedHomogeneous_C (letterWeight (ι := Fin n') (n := k)) (sigMat p n' O g a c b)
  have := h1.mul h2
  rw [add_zero] at this
  have e : (letterWeight (ι := Fin n') (n := k) (posOf n' a, c)) = (Pi.single (posOf n' a) 1 : Fin n' → ℕ) := by
    funext i
    unfold letterWeight
    simp only [Pi.single_apply]
    congr
  rw [e] at this
  exact this

def eDel (j : ℤ) : Fin n' → ℕ :=
  ∑ l : Fin r, p ^ (zF F j - F.fr j l.val).toNat • (Pi.single (posOf n' (F.fr j l.val)) 1 : Fin n' → ℕ)

def eD (s : ℤ) : Fin n' → ℕ :=
  ∑ l : Fin r, p ^ (s - Arow F s l.val).toNat • (Pi.single (posOf n' (Arow F s l.val)) 1 : Fin n' → ℕ)

/- English proof (translation)
Unfold `Del minorI`. Use `split_ifs with h`. Use `pol_det _ _ fun l b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`. Unfold `twRow`.

Conclude with `dv_pol_pow _ _ (xg_hom p n' O g _ _) _`. Conclude with `Submodule.zero_mem _`.
-/
theorem Del_hom (g : Matrix (Fin k) (Fin k) (WF p n')) (j : ℤ) :
    Del p n' O F g j ∈ Pol (KK O) k (eDel p n' F j) := by
  unfold Del minorI
  split_ifs with h
  · refine pol_det _ _ fun l b => ?_
    simp only [Matrix.of_apply]
    unfold twRow
    exact dv_pol_pow _ _ (xg_hom p n' O g _ _) _
  · exact Submodule.zero_mem _

/- English proof (translation)
Unfold `Dtop`. Use `pol_det _ _ fun l b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`. Conclude with `dv_pol_pow _ _ (xg_hom p n' O g _ _) _`.
-/
theorem Dtop_hom (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p n')) (s : ℤ) :
    Dtop p n' O F hrk g s ∈ Pol (KK O) k (eD p n' F s) := by
  unfold Dtop
  refine pol_det _ _ fun l b => ?_
  simp only [Matrix.of_apply]
  exact dv_pol_pow _ _ (xg_hom p n' O g _ _) _

def eSP (k c' Q : ℕ) : Fin n' → ℕ :=
  c' • (∑ j ∈ Finset.range F.J, alpha p F k (j : ℤ) • eDel p n' F (j : ℤ)) +
    (∑ j ∈ Finset.range F.J, c' • eDel p n' F (j : ℤ)) +
    ∑ s ∈ F.TT, ((2 * Q + 3) * c' + k * Q) • eD p n' F (s.val : ℤ)

/- English proof (translation)
Unfold `HasMultideg SPtrue eSP R0 DtopProd`. Use `dv_pol_mul _ _ _ _ (dv_pol_mul _ _ _ _ (dv_pol_pow _ _ ?_ _) ?_) ?_` and prove the remaining obligations. Conclude with `pol_prod _ _ _ fun j _ => dv_pol_pow _ _ (Del_hom p n' O F g j) _`. Conclude with `pol_prod _ _ _ fun j _ => dv_pol_pow _ _ (Del_hom p n' O F g j) _`. Conclude with `pol_prod _ _ _ fun s _ => dv_pol_pow _ _ (Dtop_hom p n' O F hrk g s.val) _`.
-/
theorem SPtrue_hom (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p n')) (c' Q : ℕ) :
    HasMultideg (SPtrue p n' O F hrk g c' Q) (eSP p n' F k c' Q) := by
  unfold HasMultideg SPtrue eSP R0 DtopProd
  refine dv_pol_mul _ _ _ _ (dv_pol_mul _ _ _ _ (dv_pol_pow _ _ ?_ _) ?_) ?_
  · exact pol_prod _ _ _ fun j _ => dv_pol_pow _ _ (Del_hom p n' O F g j) _
  · exact pol_prod _ _ _ fun j _ => dv_pol_pow _ _ (Del_hom p n' O F g j) _
  · exact pol_prod _ _ _ fun s _ => dv_pol_pow _ _ (Dtop_hom p n' O F hrk g s.val) _

end SP

end Formalism.MainNotions.Pf14
