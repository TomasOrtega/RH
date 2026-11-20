import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.WedgeCoord

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

def hl (w : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun z := herm Hm z w
  map_add' x y := by simp [herm, add_dotProduct]
  map_smul' c x := by simp [herm, smul_dotProduct]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hl_apply (w z : Fin g → ℂ) : hl Hm w z = herm Hm z w := rfl

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem herm_add_right (z w w' : Fin g → ℂ) : herm Hm z (w + w') = herm Hm z w + herm Hm z w' := by
  simp [herm, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_smul, dotProduct_smul]`.
-/
theorem herm_smul_right (z w : Fin g → ℂ) (c : ℂ) : herm Hm z (c • w) = star c * herm Hm z w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_zero_right (z : Fin g → ℂ) : herm Hm z 0 = 0 := by
  simp [herm]

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => exact herm_zero_right Hm z`. Consider the case `add x y _ _ hx hy => rw [herm_add_right, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [herm_smul_right, hx, mul_zero]`.
-/
theorem herm_eq_zero_of_mem_span {s : Set (Fin g → ℂ)} {z w : Fin g → ℂ}
    (h : ∀ v ∈ s, herm Hm z v = 0) (hw : w ∈ Submodule.span ℂ s) : herm Hm z w = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact herm_zero_right Hm z
  | add x y _ _ hx hy => rw [herm_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [herm_smul_right, hx, mul_zero]

/- English proof (translation)
Unfold `herm`. Rewrite using `[← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, Matrix.dotProduct_mulVec]`.
-/
theorem herm_symm (hH : Hm.IsHermitian) (z w : Fin g → ℂ) : herm Hm z w = star (herm Hm w z) := by
  unfold herm
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq,
    Matrix.dotProduct_mulVec]

/- English proof (translation)
Set `T : (n → ℂ) →ₗ[ℂ] (n → ℂ)` to `(LinearMap.pi fun i => hl Hm (V i)) ∘ₗ Fintype.linearCombination ℂ V`. Establish `hT : ∀ a i, T a i = herm Hm (∑ m, a m • V m) (V i)` using `fun a i => rfl`. Establish `hinj : Function.Injective T`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Establish `h0 : ∑ m, a m • V m = 0`. Assume the negation of the conclusion as `hne`. Establish `h1` using `hpos _ hne`. Establish `h2 : herm Hm (∑ m, a m • V m) (∑ m, a m • V m) = 0`. Use `herm_eq_zero_of_mem_span Hm (s := Set.range V) ?_ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[← hT, ha]`. Both sides reduce to the same expression. Conclude with `Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)`. Rewrite `h1` using `[h2]`.

Simplify using `at h1`. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.1 hV a h0 i`. Take `⟨a, ha⟩` from `LinearMap.surjective_of_injective hinj c`. Conclude with `⟨a, fun i => by rw [← hT, ha]⟩`.
-/
theorem gram_surj (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) {n : Type} [Fintype n]
    (V : n → Fin g → ℂ) (hV : LinearIndependent ℂ V) (c : n → ℂ) :
    ∃ a : n → ℂ, ∀ i, herm Hm (∑ m, a m • V m) (V i) = c i := by
  classical
  let T : (n → ℂ) →ₗ[ℂ] (n → ℂ) :=
    (LinearMap.pi fun i => hl Hm (V i)) ∘ₗ Fintype.linearCombination ℂ V
  have hT : ∀ a i, T a i = herm Hm (∑ m, a m • V m) (V i) := fun a i => rfl
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h0 : ∑ m, a m • V m = 0 := by
      by_contra hne
      have h1 := hpos _ hne
      have h2 : herm Hm (∑ m, a m • V m) (∑ m, a m • V m) = 0 := by
        refine herm_eq_zero_of_mem_span Hm (s := Set.range V) ?_ ?_
        · rintro _ ⟨i, rfl⟩
          rw [← hT, ha]; rfl
        · exact Submodule.sum_mem _ fun m _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      rw [h2] at h1
      simp at h1
    funext i
    exact Fintype.linearIndependent_iff.1 hV a h0 i
  obtain ⟨a, ha⟩ := LinearMap.surjective_of_injective hinj c
  exact ⟨a, fun i => by rw [← hT, ha]⟩

/- English proof (translation)
Take `⟨s, hsV, hspan, hli⟩` from `exists_linearIndependent ℂ (Set.range V)`. Establish `hfin : s.Finite` using `(Set.finite_range V).subset hsV`. Use `haveI := hfin.fintype`. Take `⟨c, hc⟩` from `gram_surj Hm hpos (fun v : s => (v : Fin g → ℂ)) hli (fun v => herm Hm y v)`. Establish `hmem : ∑ m : s, c m • (m : Fin g → ℂ) ∈ Submodule.span ℂ (Set.range V)` using `Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span (hsV m.2))`.

Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem`. Use `⟨a, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[ha]`. Use `herm_eq_zero_of_mem_span Hm (s := s) ?_ ?_` and prove the remaining obligations. Introduce `v hv`.

Rewrite using `[← hl_apply, map_sub, hl_apply, hl_apply, hc ⟨v, hv⟩, sub_self]`. Rewrite using `[hspan]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.
-/
theorem exists_proj (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) {p : ℕ}
    (V : Fin p → Fin g → ℂ) (y : Fin g → ℂ) :
    ∃ a : Fin p → ℂ, ∀ i, herm Hm (y - ∑ m, a m • V m) (V i) = 0 := by
  classical
  obtain ⟨s, hsV, hspan, hli⟩ := exists_linearIndependent ℂ (Set.range V)
  have hfin : s.Finite := (Set.finite_range V).subset hsV
  haveI := hfin.fintype
  obtain ⟨c, hc⟩ := gram_surj Hm hpos (fun v : s => (v : Fin g → ℂ)) hli (fun v => herm Hm y v)
  have hmem : ∑ m : s, c m • (m : Fin g → ℂ) ∈ Submodule.span ℂ (Set.range V) :=
    Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span (hsV m.2))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨a, fun i => ?_⟩
  rw [ha]
  refine herm_eq_zero_of_mem_span Hm (s := s) ?_ ?_
  · intro v hv
    rw [← hl_apply, map_sub, hl_apply, hl_apply, hc ⟨v, hv⟩, sub_self]
  · rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩

end GlobalTheory.DetLine.WedgeCoord

open GlobalTheory.DetLine.WedgeCoord in
/- English proof (translation)
Introduce `g p q Hm V W hH hpos`. Use `⟨fun x => ?_, fun hV hW => ?_⟩` and prove the remaining obligations. Use `choose a ha using fun k => exists_proj Hm hpos V (x k)`. Conclude with `⟨_, a, ha, rfl⟩`. Set `P : Type` to `{z : (Fin g → ℂ) × (Fin p → ℂ) // ∀ i, herm Hm (z.1 - ∑ m, z.2 m • V m) (V i) = 0}`.

Set `r : P → (Fin q ⊕ Fin p → ℂ)` to `fun z => Sum.elim (fun j => -(Real.pi : ℂ) * herm Hm (W j) z.1.1) (fun i => z.1.2 i)`. Establish `key : ∀ z : P, Sum.elim (fun j => -(Real.pi : ℂ) * herm Hm (W j) z.1.1) (0 : Fin p → ℂ) ∈ Submodule.span ℂ (Set.range r) ∧ Sum.elim (0 : Fin q → ℂ) z.1.2 ∈ Submodule.span ℂ (Set.range r)`. Introduce `z`. Set `z' : P` to `⟨(Complex.I • z.1.1, Complex.I • z.1.2), fun i => by`. Establish `: Complex.I • z.1.1 - ∑ m, (Complex.I • z.1.2) m • V m = Complex.I • (z.1.1 - ∑ m, z.1.2 m • V m)`.

Simplify using `only [smul_sub, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, mul_smul]`. Use `show herm Hm (Complex.I • z.1.1 - ∑ m, (Complex.I • z.1.2) m • V m) (V i) = 0`. Rewrite using `[this, ← hl_apply, map_smul, hl_apply, z.2 i, smul_zero]⟩`. Establish `h1 : r z ∈ Submodule.span ℂ (Set.range r)` using `Submodule.subset_span ⟨z, rfl⟩`. Establish `h2 : r z' ∈ Submodule.span ℂ (Set.range r)` using `Submodule.subset_span ⟨z', rfl⟩`.

Establish `hI` using `Complex.I_mul_I`. Prove the components needed by the constructor for the conclusion. Use `Submodule.smul_mem _ (1/2 : ℂ) (Submodule.add_mem _ h1 (Submodule.smul_mem _ Complex.I h2)) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Break down `k with j | i` into its components or cases.

Simplify using `only [r, z', Sum.elim_inl, Pi.smul_apply, Pi.add_apply, smul_eq_mul, herm_smul_right, Complex.star_def, Complex.conj_I]`. Take the linear combination `(-(1/2) * (Real.pi : ℂ) * herm Hm (W j) z.1.1) * hI`. Simplify using `only [r, z', Sum.elim_inr, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply]`. Take the linear combination `(-(1/2) * z.1.2 i) * hI`. Use `Submodule.smul_mem _ (1/2 : ℂ) (Submodule.sub_mem _ h1 (Submodule.smul_mem _ Complex.I h2)) using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k`. Break down `k with j | i` into its components or cases. Simplify using `only [r, z', Sum.elim_inl, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, herm_smul_right, Complex.star_def, Complex.conj_I, Pi.zero_apply]`. Take the linear combination `((1/2) * (Real.pi : ℂ) * herm Hm (W j) z.1.1) * hI`. Simplify using `only [r, z', Sum.elim_inr, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`.

Take the linear combination `((1/2) * z.1.2 i) * hI`. Establish `hspan : Submodule.span ℂ (Set.range r) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `u _`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`.

Take `⟨c, hc⟩` from `gram_surj Hm hpos W hW (fun j => star (u (Sum.inl j) / (-(Real.pi : ℂ))))`. Take `⟨a, ha⟩` from `exists_proj Hm hpos V (∑ m, c m • W m)`. Establish `h1` using `(key ⟨(∑ m, c m • W m, a), ha⟩).1`. Establish `h2` using `(key ⟨(∑ m, u (Sum.inr m) • V m, fun m => u (Sum.inr m)), fun i => by`. Simplify using `[herm]⟩).2`.

Use `Submodule.add_mem _ h1 h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Break down `k with j | i` into its components or cases. Simplify using `only [Sum.elim_inl, Pi.add_apply, Pi.zero_apply, add_zero]`. Rewrite using `[herm_symm Hm hH, hc, star_star]`.

Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hz : (Matrix.detRowAlternating (n` using `Fin q ⊕ Fin p) (R := ℂ)).toMultilinearMap = 0 := by`.

Use `MultilinearMap.ext_of_span_eq_top (g := fun _ => r) (fun _ => hspan) fun s => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hcon (fun k => (s k).1.1) _ hne ⟨fun k => (s k).1.2, fun k => (s k).2, rfl⟩`. Use `congrArg (fun f => f (1 : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ)) hz` as an intermediate fact. Establish `h1 : Matrix.det (1 : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) = 0` using `this`.

Simplify using `at h1`.
-/
theorem GlobalTheory.DetLine.exists_wedgeCoord : ∀ (g p q : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) → (∀ x, ∃ Δ, IsWedgeCoord Hm V W x Δ) ∧ (LinearIndependent ℂ V → LinearIndependent ℂ W → ∃ x Δ, Δ ≠ 0 ∧ IsWedgeCoord Hm V W x Δ) := by
  intro g p q Hm V W hH hpos
  refine ⟨fun x => ?_, fun hV hW => ?_⟩
  · choose a ha using fun k => exists_proj Hm hpos V (x k)
    exact ⟨_, a, ha, rfl⟩
  · classical
    let P : Type := {z : (Fin g → ℂ) × (Fin p → ℂ) //
      ∀ i, herm Hm (z.1 - ∑ m, z.2 m • V m) (V i) = 0}
    let r : P → (Fin q ⊕ Fin p → ℂ) := fun z =>
      Sum.elim (fun j => -(Real.pi : ℂ) * herm Hm (W j) z.1.1) (fun i => z.1.2 i)
    have key : ∀ z : P, Sum.elim (fun j => -(Real.pi : ℂ) * herm Hm (W j) z.1.1) (0 : Fin p → ℂ) ∈
        Submodule.span ℂ (Set.range r) ∧
        Sum.elim (0 : Fin q → ℂ) z.1.2 ∈ Submodule.span ℂ (Set.range r) := by
      intro z
      let z' : P := ⟨(Complex.I • z.1.1, Complex.I • z.1.2), fun i => by
        have : Complex.I • z.1.1 - ∑ m, (Complex.I • z.1.2) m • V m =
            Complex.I • (z.1.1 - ∑ m, z.1.2 m • V m) := by
          simp only [smul_sub, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, mul_smul]
        show herm Hm (Complex.I • z.1.1 - ∑ m, (Complex.I • z.1.2) m • V m) (V i) = 0
        rw [this, ← hl_apply, map_smul, hl_apply, z.2 i, smul_zero]⟩
      have h1 : r z ∈ Submodule.span ℂ (Set.range r) := Submodule.subset_span ⟨z, rfl⟩
      have h2 : r z' ∈ Submodule.span ℂ (Set.range r) := Submodule.subset_span ⟨z', rfl⟩
      have hI := Complex.I_mul_I
      constructor
      · convert Submodule.smul_mem _ (1/2 : ℂ) (Submodule.add_mem _ h1
          (Submodule.smul_mem _ Complex.I h2)) using 1
        funext k
        rcases k with j | i
        · simp only [r, z', Sum.elim_inl, Pi.smul_apply, Pi.add_apply, smul_eq_mul, herm_smul_right,
            Complex.star_def, Complex.conj_I]
          linear_combination (-(1/2) * (Real.pi : ℂ) * herm Hm (W j) z.1.1) * hI
        · simp only [r, z', Sum.elim_inr, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply]
          linear_combination (-(1/2) * z.1.2 i) * hI
      · convert Submodule.smul_mem _ (1/2 : ℂ) (Submodule.sub_mem _ h1
          (Submodule.smul_mem _ Complex.I h2)) using 1
        funext k
        rcases k with j | i
        · simp only [r, z', Sum.elim_inl, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, herm_smul_right,
            Complex.star_def, Complex.conj_I, Pi.zero_apply]
          linear_combination ((1/2) * (Real.pi : ℂ) * herm Hm (W j) z.1.1) * hI
        · simp only [r, z', Sum.elim_inr, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          linear_combination ((1/2) * z.1.2 i) * hI
    have hspan : Submodule.span ℂ (Set.range r) = ⊤ := by
      rw [eq_top_iff]
      intro u _
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      obtain ⟨c, hc⟩ := gram_surj Hm hpos W hW (fun j => star (u (Sum.inl j) / (-(Real.pi : ℂ))))
      obtain ⟨a, ha⟩ := exists_proj Hm hpos V (∑ m, c m • W m)
      have h1 := (key ⟨(∑ m, c m • W m, a), ha⟩).1
      have h2 := (key ⟨(∑ m, u (Sum.inr m) • V m, fun m => u (Sum.inr m)), fun i => by
        simp [herm]⟩).2
      convert Submodule.add_mem _ h1 h2 using 1
      funext k
      rcases k with j | i
      · simp only [Sum.elim_inl, Pi.add_apply, Pi.zero_apply, add_zero]
        rw [herm_symm Hm hH, hc, star_star]
        field_simp
      · simp
    by_contra hcon
    push_neg at hcon
    have hz : (Matrix.detRowAlternating (n := Fin q ⊕ Fin p) (R := ℂ)).toMultilinearMap = 0 := by
      refine MultilinearMap.ext_of_span_eq_top (g := fun _ => r) (fun _ => hspan) fun s => ?_
      by_contra hne
      exact hcon (fun k => (s k).1.1) _ hne ⟨fun k => (s k).1.2, fun k => (s k).2, rfl⟩
    have := congrArg (fun f => f (1 : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ)) hz
    have h1 : Matrix.det (1 : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) = 0 := this
    simp at h1
