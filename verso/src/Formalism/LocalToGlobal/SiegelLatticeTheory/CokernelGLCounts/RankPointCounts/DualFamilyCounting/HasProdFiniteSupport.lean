import Mathlib

noncomputable section

namespace Formalism.L2.SG.Pf.HasProdFiniteSupport

open Filter Topology

variable {ι : Type*}

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem hasProd_inv₀' {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  unfold HasProd at h ⊢
  refine (h.inv₀ ha).congr (fun s => ?_)
  exact (Finset.prod_inv_distrib f).symm

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem hasProd_rpow' {f : ι → ℝ} {a : ℝ} (p : ℝ) (hf : ∀ i, 0 ≤ f i) (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => f i ^ p) (a ^ p) := by
  unfold HasProd at h ⊢
  refine (h.rpow_const (Or.inl ha)).congr (fun s => ?_)
  exact (Real.finsetProd_rpow s f (fun i _ => hf i) p).symm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem hasProd_of_compl (P : ι → Prop) [DecidablePred P] [Fintype {i // P i}] {f : ι → ℝ} {a : ℝ}
    (h : HasProd (fun i : {i // ¬ P i} => f i) a) : HasProd f (a * ∏ i : {i // P i}, f i) := by
  have h1 : HasProd ({i | ¬ P i}.mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := {i | ¬ P i})).mp h
  have h2 : HasProd ({i | P i}.mulIndicator f) (∏ i : {i // P i}, f i) :=
    letI : Fintype ({i | P i} : Set ι) := inferInstanceAs (Fintype {i // P i})
    (hasProd_subtype_iff_mulIndicator (s := {i | P i})).mp (hasProd_fintype _)
  have h3 := h1.mul h2
  convert h3 using 1
  funext i
  by_cases hp : P i <;> simp [Set.mulIndicator, hp]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem hasProd_compl_of (P : ι → Prop) [DecidablePred P] [Fintype {i // P i}] {f : ι → ℝ} {a : ℝ}
    (h : HasProd f a) (hf : ∀ i, P i → f i ≠ 0) :
    HasProd (fun i : {i // ¬ P i} => f i) (a * (∏ i : {i // P i}, f i)⁻¹) := by
  have h2 : HasProd (fun i => ({i | P i}.mulIndicator f i)⁻¹) (∏ i : {i // P i}, f i)⁻¹ := by
    have h0 : HasProd ({i | P i}.mulIndicator f) (∏ i : {i // P i}, f i) :=
      letI : Fintype ({i | P i} : Set ι) := inferInstanceAs (Fintype {i // P i})
    (hasProd_subtype_iff_mulIndicator (s := {i | P i})).mp (hasProd_fintype _)
    exact hasProd_inv₀' h0 (Finset.prod_ne_zero_iff.mpr fun i _ => hf i i.2)
  have h3 := h.mul h2
  have h4 : HasProd ({i | ¬ P i}.mulIndicator f) (a * (∏ i : {i // P i}, f i)⁻¹) := by
    convert h3 using 1
    funext i
    by_cases hp : P i
    · simp [Set.mulIndicator, hp, hf i hp]
    · simp [Set.mulIndicator, hp]
  exact (hasProd_subtype_iff_mulIndicator (s := {i | ¬ P i})).mpr h4

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hasProd_of_finite_support {f : ι → ℝ} (s : Set ι) (hs : s.Finite) (h1 : ∀ i ∉ s, f i = 1) :
    HasProd f (∏ i ∈ hs.toFinset, f i) :=
  hasProd_prod_of_ne_finset_one (fun i hi => h1 i (by simpa using hi))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem hasProd_of_compl' (s : Finset ι) {f : ι → ℝ} {a : ℝ}
    (h : HasProd (fun i : {i // i ∉ s} => f i) a) : HasProd f (a * ∏ i : s, f i) := by
  classical
  have h1 : HasProd ((↑s : Set ι)ᶜ.mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι)ᶜ)).mp h
  have h2 : HasProd ((↑s : Set ι).mulIndicator f) (∏ i : s, f i) :=
    (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι))).mp (hasProd_fintype _)
  have h3 := h1.mul h2
  convert h3 using 1
  · funext i
    by_cases hp : i ∈ s <;> simp [Set.mulIndicator, hp]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hasProd_compl_of' (s : Finset ι) {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (hf : ∀ i ∈ s, f i ≠ 0) :
    HasProd (fun i : {i // i ∉ s} => f i) (a * (∏ i : s, f i)⁻¹) := by
  classical
  have h2 : HasProd (fun i => ((↑s : Set ι).mulIndicator f i)⁻¹) (∏ i : s, f i)⁻¹ := by
    have h0 : HasProd ((↑s : Set ι).mulIndicator f) (∏ i : s, f i) :=
      (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι))).mp (hasProd_fintype _)
    exact hasProd_inv₀' h0 (Finset.prod_ne_zero_iff.mpr fun i _ => hf i i.2)
  have h3 := h.mul h2
  have h4 : HasProd ((↑s : Set ι)ᶜ.mulIndicator f) (a * (∏ i : s, f i)⁻¹) := by
    convert h3 using 1
    funext i
    by_cases hp : i ∈ s
    · simp [Set.mulIndicator, hp, hf i hp]
    · simp [Set.mulIndicator, hp]
  exact (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι)ᶜ)).mpr h4

end Formalism.L2.SG.Pf.HasProdFiniteSupport
