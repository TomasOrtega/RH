import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithClassFormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianBundleCanonicalOfVerticalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorOfTensorSectionAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalBundleClassInRadicalStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

section Eqv

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k}

/- English proof (translation)
The claim follows from `e ▸ h`.
-/
theorem isEqn_of_eq {D : CartierDiv X} {x : X} {g g' : X.functionFieldˣ} (h : D.IsEqn x g) (e : g = g') :
    D.IsEqn x g' := e ▸ h

/- English proof (translation)
Take `⟨ρ, hρ, h⟩` from `hL`. Take `⟨r, hr, rfl⟩` from `hM`. Take `⟨s, hs, hd⟩` from `(GlobalTheory.T.divisor_of_tensor_section_add k X q L M).2 ρ hρ r hr`. Conclude with `⟨s, hs, fun x hx => by rw [hd]; exact isEqn_of_eq ((h x hx).add (hE x hx)) (hb x hx)⟩`.
-/
theorem rep_tens {p : ℕ} {L M : HermLB q} {E : CartierDiv X} {b e b' : X → X.functionFieldˣ} (hL : Rep p L b)
    (hM : ∃ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), M.div hr = E) (hE : ∀ x, Ov p x → E.IsEqn x (e x))
    (hb : ∀ x, Ov p x → b x * e x = b' x) : Rep p (L.tens M) b' := by
  obtain ⟨ρ, hρ, h⟩ := hL
  obtain ⟨r, hr, rfl⟩ := hM
  obtain ⟨s, hs, hd⟩ := (GlobalTheory.T.divisor_of_tensor_section_add k X q L M).2 ρ hρ r hr
  exact ⟨s, hs, fun x hx => by rw [hd]; exact isEqn_of_eq ((h x hx).add (hE x hx)) (hb x hx)⟩

/- English proof (translation)
The claim follows from `let ⟨r, hr, h₁, _⟩ := h; ⟨r, hr, h₁⟩`.
-/
theorem Can.sec {M : HermLB q} {E : CartierDiv X} (h : Can M E) :
    ∃ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), M.div hr = E :=
  let ⟨r, hr, h₁, _⟩ := h; ⟨r, hr, h₁⟩

variable {n : ℕ} {num : Form (Cl q) (n + 1)} {N : ℕ}

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun i _ => bil_congr _ hs (h i) (h i)`.
-/
theorem sum_bil_congr (hs : IsSymm num) (G : Fin n → HermLB q) {a a' : Fin N → Cl q} (h : ∀ i, a i - a' i ∈ rad num) :
    ∑ i, bil num (fun j => cl (G j)) (a i) (a i) = ∑ i, bil num (fun j => cl (G j)) (a' i) (a' i) :=
  Finset.sum_congr rfl fun i _ => bil_congr _ hs (h i) (h i)

/- English proof (translation)
Introduce `hP k _ X _ q n hX num hnum hs G p m N hp`. Take `⟨hT, hD, -, -⟩` from `arForm_rad_rules hP.p4 k X q (n + 1) hX num hnum`. Establish `hZ` using `GlobalTheory.T.canonical_bundle_class_in_radical hP k X q n hX num hnum hs`. Use `⟨fun c => ?_, fun {c c'} h => ?_, fun {c c' c''} h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `hV : Vert p (0 : CartierDiv X)` using `fun x _ => CartierDiv.isEqn_zero x`.

Take `⟨M, hM⟩` from `GlobalTheory.T.exists_hermitian_bundle_canonical_of_vertical k X q p hp.ne_zero 0 hV`. Use `⟨fun _ => M, fun _ => 0, fun i => ⟨hM, hV, fun x _ => isEqn_of_eq (CartierDiv.isEqn_zero x) (by simp)⟩, fun L _ => sum_bil_congr hs G fun i => ?_⟩` and prove the remaining obligations. Simplify using `using hZ M hM`. Take `⟨Δ, E, hE, hS⟩` from `h`. Establish `hC : ∀ i, Can (Δ i).dual (-E i)` using `fun i => ((GlobalTheory.T.divisor_of_tensor_section_add k X q (Δ i) (Δ i)).1 _ _ (hE i).1 (hE i).1).2`.

Use `⟨fun i => (Δ i).dual, fun i => -E i, fun i => ⟨hC i, fun x hx => isEqn_of_eq ((hE i).2.1 x hx).neg inv_one, fun x hx => isEqn_of_eq ((hE i).2.2 x hx).neg (by rw [← inv_pow, inv_div])⟩, fun L' hL' => ?_⟩` and prove the remaining obligations. Establish `hR : ∀ i, Rep p ((L' i).tens (Δ i).dual) fun x => c x i ^ m` using `fun i => rep_tens (hL' i) (hC i).sec (fun x hx => ((hE i).2.2 x hx).neg) fun x _ => by`. Rewrite using `[← inv_pow, ← mul_pow, inv_div, mul_div_cancel]`. Use `hS _ hR` as an intermediate fact. Rewrite using `[sum_bil_congr hs G (a' := fun i => cl ((L' i).tens (Δ i).dual)) (fun i => by`.

Simplify using `using neg_mem (hT (L' i) (Δ i).dual)), ← this]`. Use `sum_bil_congr hs G fun i => ?_` and prove the remaining obligations. Establish `e : cl ((L' i).tens (Δ i).dual) + cl (Δ i) - cl (L' i) = (cl ((L' i).tens (Δ i).dual) - (cl (L' i) + cl (Δ i).dual)) + (cl (Δ i).dual + cl (Δ i))` using `by abel`. Rewrite using `[e]`. Conclude with `add_mem (hT _ _) (hD _)`.

Take `⟨Δ₁, E₁, hE₁, hS₁⟩` from `h₁`. Take `⟨Δ₂, E₂, hE₂, hS₂⟩` from `h₂`. Use `⟨fun i => (Δ₁ i).tens (Δ₂ i), fun i => E₁ i + E₂ i, fun i => ⟨((GlobalTheory.T.divisor_of_tensor_section_add k X q (Δ₁ i) (Δ₂ i)).1 _ _ (hE₁ i).1 (hE₂ i).1).1, fun x hx => isEqn_of_eq (((hE₁ i).2.1 x hx).add ((hE₂ i).2.1 x hx)) (mul_one 1), fun x hx => isEqn_of_eq (((hE₁ i).2.2 x …` and prove the remaining obligations. Establish `hR : ∀ i, Rep p ((L i).tens (Δ₁ i)) fun x => c' x i ^ m` using `fun i => rep_tens (hL i) (hE₁ i).1.sec (hE₁ i).2.2 fun x _ => by rw [← mul_pow, mul_div_cancel]`. Rewrite using `[← hS₁ L hL, sum_bil_congr hs G (a' := fun i => cl ((L i).tens (Δ₁ i)) + cl (Δ₂ i)) (fun i => ?_), hS₂ _ hR]`.

Use `sum_bil_congr hs G fun i => ?_` and prove the remaining obligations. Simplify using `using hT (L i) (Δ₁ i)`. Establish `e : cl (L i) + cl ((Δ₁ i).tens (Δ₂ i)) - (cl ((L i).tens (Δ₁ i)) + cl (Δ₂ i)) = (cl ((Δ₁ i).tens (Δ₂ i)) - (cl (Δ₁ i) + cl (Δ₂ i))) - (cl ((L i).tens (Δ₁ i)) - (cl (L i) + cl (Δ₁ i)))`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `sub_mem (hT _ _) (hT _ _)`.
-/
theorem moves_equivalence : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (n : ℕ),
    IsArithVar q (n + 1) → ∀ num : Form (Cl q) (n + 1), IsArForm (n + 1) num → IsSymm num →
    ∀ (G : Fin n → HermLB q) (p m N : ℕ), p.Prime → Equivalence (Moves (N := N) num G p m) := by
  intro hP k _ X _ q n hX num hnum hs G p m N hp
  obtain ⟨hT, hD, -, -⟩ := arForm_rad_rules hP.p4 k X q (n + 1) hX num hnum
  have hZ := GlobalTheory.T.canonical_bundle_class_in_radical hP k X q n hX num hnum hs
  refine ⟨fun c => ?_, fun {c c'} h => ?_, fun {c c' c''} h₁ h₂ => ?_⟩
  ·
    have hV : Vert p (0 : CartierDiv X) := fun x _ => CartierDiv.isEqn_zero x
    obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitian_bundle_canonical_of_vertical k X q p hp.ne_zero 0 hV
    refine ⟨fun _ => M, fun _ => 0, fun i => ⟨hM, hV, fun x _ => isEqn_of_eq (CartierDiv.isEqn_zero x) (by simp)⟩,
      fun L _ => sum_bil_congr hs G fun i => ?_⟩
    simpa using hZ M hM
  ·
    obtain ⟨Δ, E, hE, hS⟩ := h
    have hC : ∀ i, Can (Δ i).dual (-E i) := fun i => ((GlobalTheory.T.divisor_of_tensor_section_add k X q (Δ i) (Δ i)).1 _ _ (hE i).1 (hE i).1).2
    refine ⟨fun i => (Δ i).dual, fun i => -E i, fun i => ⟨hC i, fun x hx => isEqn_of_eq ((hE i).2.1 x hx).neg inv_one,
      fun x hx => isEqn_of_eq ((hE i).2.2 x hx).neg (by rw [← inv_pow, inv_div])⟩, fun L' hL' => ?_⟩
    have hR : ∀ i, Rep p ((L' i).tens (Δ i).dual) fun x => c x i ^ m := fun i =>
      rep_tens (hL' i) (hC i).sec (fun x hx => ((hE i).2.2 x hx).neg) fun x _ => by
        rw [← inv_pow, ← mul_pow, inv_div, mul_div_cancel]
    have := hS _ hR
    rw [sum_bil_congr hs G (a' := fun i => cl ((L' i).tens (Δ i).dual)) (fun i => by
      simpa using neg_mem (hT (L' i) (Δ i).dual)), ← this]
    refine sum_bil_congr hs G fun i => ?_
    have e : cl ((L' i).tens (Δ i).dual) + cl (Δ i) - cl (L' i) =
        (cl ((L' i).tens (Δ i).dual) - (cl (L' i) + cl (Δ i).dual)) + (cl (Δ i).dual + cl (Δ i)) := by abel
    rw [e]
    exact add_mem (hT _ _) (hD _)
  ·
    obtain ⟨Δ₁, E₁, hE₁, hS₁⟩ := h₁
    obtain ⟨Δ₂, E₂, hE₂, hS₂⟩ := h₂
    refine ⟨fun i => (Δ₁ i).tens (Δ₂ i), fun i => E₁ i + E₂ i, fun i =>
      ⟨((GlobalTheory.T.divisor_of_tensor_section_add k X q (Δ₁ i) (Δ₂ i)).1 _ _ (hE₁ i).1 (hE₂ i).1).1,
        fun x hx => isEqn_of_eq (((hE₁ i).2.1 x hx).add ((hE₂ i).2.1 x hx)) (mul_one 1),
        fun x hx => isEqn_of_eq (((hE₁ i).2.2 x hx).add ((hE₂ i).2.2 x hx)) (by rw [← mul_pow, mul_comm (c' x i / c x i), div_mul_div_cancel])⟩,
      fun L hL => ?_⟩
    have hR : ∀ i, Rep p ((L i).tens (Δ₁ i)) fun x => c' x i ^ m := fun i =>
      rep_tens (hL i) (hE₁ i).1.sec (hE₁ i).2.2 fun x _ => by rw [← mul_pow, mul_div_cancel]
    rw [← hS₁ L hL, sum_bil_congr hs G (a' := fun i => cl ((L i).tens (Δ₁ i)) + cl (Δ₂ i)) (fun i => ?_), hS₂ _ hR]
    · refine sum_bil_congr hs G fun i => ?_
      simpa using hT (L i) (Δ₁ i)
    · have e : cl (L i) + cl ((Δ₁ i).tens (Δ₂ i)) - (cl ((L i).tens (Δ₁ i)) + cl (Δ₂ i)) =
          (cl ((Δ₁ i).tens (Δ₂ i)) - (cl (Δ₁ i) + cl (Δ₂ i))) - (cl ((L i).tens (Δ₁ i)) - (cl (L i) + cl (Δ₁ i))) := by
        abel
      rw [e]
      exact sub_mem (hT _ _) (hT _ _)

end Eqv

end GlobalTheory.LatChain

end
