import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorOfTensorSectionAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalBundleClassInRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithClassFormPropertiesStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

/- English proof (translation)
Establish `hc : Nat.Coprime p p'` using `(Nat.coprime_primes hp hp').2 hne`. Establish `e : ((p : ℤ) * Nat.gcdA p p' + (p' : ℤ) * Nat.gcdB p p' : ℤ) = 1`. Rewrite using `[← Nat.gcd_eq_gcd_ab, hc]`. Both sides reduce to the same expression. Establish `e' : (p : X.presheaf.stalk x) * (Nat.gcdA p p' : X.presheaf.stalk x) + (p' : X.presheaf.stalk x) * (Nat.gcdB p p' : X.presheaf.stalk x) = 1`.

Conclude with `congrArg (Int.cast : ℤ → X.presheaf.stalk x) e` after adjusting the coercions. Establish `m₁ : (p : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)` using `h₁`. Establish `m₂ : (p' : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)` using `h₂`. Establish `h1 : (1 : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)`. Rewrite using `[← e']`.

Conclude with `add_mem (Ideal.mul_mem_right _ _ m₁) (Ideal.mul_mem_right _ _ m₂)`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)`.
-/
theorem not_ov_and_ov {X : Scheme.{0}} {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') (x : X)
    (h₁ : Ov p x) (h₂ : Ov p' x) : False := by
  have hc : Nat.Coprime p p' := (Nat.coprime_primes hp hp').2 hne
  have e : ((p : ℤ) * Nat.gcdA p p' + (p' : ℤ) * Nat.gcdB p p' : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc]; rfl
  have e' : (p : X.presheaf.stalk x) * (Nat.gcdA p p' : X.presheaf.stalk x) +
      (p' : X.presheaf.stalk x) * (Nat.gcdB p p' : X.presheaf.stalk x) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → X.presheaf.stalk x) e
  have m₁ : (p : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := h₁
  have m₂ : (p' : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := h₂
  have h1 : (1 : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [← e']; exact add_mem (Ideal.mul_mem_right _ _ m₁) (Ideal.mul_mem_right _ _ m₂)
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

/- English proof (translation)
Introduce `hP k _ X _ q n hX num hnum hs G m N c c' L' S`. Establish `R` using `GlobalTheory.T.arith_class_form_properties hP.p4 k X q (n + 1) hX num hnum`. Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Introduce `_ L Q E h`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Take `⟨hQ, hL, hE, -⟩` from `h i`. Establish `hE0 : E i = 0` using `CartierDiv.ext_of_isEqn fun x => ⟨1, hE x (by simp), CartierDiv.isEqn_zero x⟩`. Establish `hq` using `GlobalTheory.T.canonical_bundle_class_in_radical hP k X q n hX num hnum hs (Q i) (hE0 ▸ hQ)`. Establish `hd : cl (L' i) - cl (L i) ∈ rad num`. Use `add_mem hL hq using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Conclude with `bil_congr _ hs hd hd`. Introduce `p S hpS ih hS L Q E h`. Take `⟨hp, Δ, EΔ, hΔ, hmove⟩` from `hS p (Finset.mem_insert_self p S)`. Establish `hS' : ∀ p' ∈ S, p'.Prime ∧ Moves num G p' m (c p') (c' p')` using `fun p' hp' => hS p' (Finset.mem_insert_of_mem hp')`.

Establish `hRep : ∀ i, Rep p (L i) fun x => c p x i ^ m` using `fun i => ((h i).2.2.2 p (Finset.mem_insert_self p S)).1`. Establish `hsum` using `hmove L hRep`. Use `(ih hS' (fun i => (L i).tens (Δ i)) (fun i => (Q i).tens (Δ i).dual) (fun i => E i + -EΔ i) fun i => ?_).trans ?_` and prove the remaining obligations. Take `⟨hQ, hL, hE, hRp⟩` from `h i`. Take `⟨hΔc, hΔv, hΔe⟩` from `hΔ i`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((GlobalTheory.T.divisor_of_tensor_section_add k X q (Q i) (Δ i).dual).1 (E i) (-EΔ i) hQ ((GlobalTheory.T.divisor_of_tensor_section_add k X q (Δ i) (Δ i)).1 (EΔ i) (EΔ i) hΔc hΔc).2).1`. Establish `h1` using `R.1 (L i) (Δ i)`. Establish `h2` using `R.1 (Q i) (Δ i).dual`. Establish `h3` using `R.2.1 (Δ i)`.

Use `sub_mem (sub_mem (sub_mem hL h1) h2) h3 using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Introduce `x hx`. Distinguish the cases in `hpx : Ov p x`. Establish `e` using `((hRp p (Finset.mem_insert_self p S)).2 x hpx).add (hΔe x hpx).neg`.

Rewrite `e` using `[mul_inv_cancel]`. Then use the resulting hypothesis. Establish `e` using `(hE x fun p'' hp'' => by`. Break down `Finset.mem_insert.1 hp'' with rfl | hp''` into its components or cases. Use `exacts [hpx, hx p'' hp'']).add (hΔv x hpx).neg`. Rewrite `e` using `[inv_one, mul_one]`. Then use the resulting hypothesis.

Introduce `p' hp'S`. Take `⟨hRepp', hEp'⟩` from `hRp p' (Finset.mem_insert_of_mem hp'S)`. Establish `hp'p : p' ≠ p` using `fun e => hpS (e ▸ hp'S)`. Establish `nov : ∀ x : X, Ov p' x → ¬ Ov p x` using `fun x h₁ h₂ => not_ov_and_ov (hS p' (Finset.mem_insert_of_mem hp'S)).1 hp hp'p x h₁ h₂`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨ρ, hρ, hρe⟩` from `hRepp'`. Take `⟨r, hr, hrd, -⟩` from `hΔc`. Take `⟨s, hs', hsd⟩` from `(GlobalTheory.T.divisor_of_tensor_section_add k X q (L i) (Δ i)).2 ρ hρ r hr`. Use `⟨s, hs', fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[hsd, hrd]`.

Establish `e` using `(hρe x hx).add (hΔv x (nov x hx))`. Rewrite `e` using `[mul_one]`. Then use the resulting hypothesis. Establish `e` using `(hEp' x hx).add (hΔv x (nov x hx)).neg`. Rewrite `e` using `[inv_one, mul_one]`. Then use the resulting hypothesis. Rewrite using `[← hsum]`.

Conclude with `Finset.sum_congr rfl fun i _ => bil_congr _ hs (R.1 _ _) (R.1 _ _)`.
-/
theorem bil_sum_eq_of_moves : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (n : ℕ), IsArithVar q (n + 1) → ∀ num : Form (Cl q) (n + 1), IsArForm (n + 1) num → IsSymm num → ∀ (G : Fin n → HermLB q) (m N : ℕ) (c c' : ℕ → X → Fin N → X.functionFieldˣ) (L' : Fin N → HermLB q) (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ Moves num G p m (c p) (c' p)) → ∀ (L Q : Fin N → HermLB q) (E : Fin N → CartierDiv X), (∀ i, Can (Q i) (E i) ∧ cl (L' i) - (cl (L i) + cl (Q i)) ∈ rad num ∧ (∀ x, (∀ p ∈ S, ¬ Ov p x) → (E i).IsEqn x 1) ∧ ∀ p ∈ S, (Rep p (L i) fun x => c p x i ^ m) ∧ ∀ x, Ov p x → (E i).IsEqn x ((c' p x i / c p x i) ^ m)) → ∑ i, bil num (fun j => cl (G j)) (cl (L' i)) (cl (L' i)) = ∑ i, bil num (fun j => cl (G j)) (cl (L i)) (cl (L i)) := by
  intro hP k _ X _ q n hX num hnum hs G m N c c' L' S
  have R := GlobalTheory.T.arith_class_form_properties hP.p4 k X q (n + 1) hX num hnum
  refine Finset.induction_on S ?_ ?_
  · intro _ L Q E h
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨hQ, hL, hE, -⟩ := h i
    have hE0 : E i = 0 := CartierDiv.ext_of_isEqn fun x => ⟨1, hE x (by simp), CartierDiv.isEqn_zero x⟩
    have hq := GlobalTheory.T.canonical_bundle_class_in_radical hP k X q n hX num hnum hs (Q i) (hE0 ▸ hQ)
    have hd : cl (L' i) - cl (L i) ∈ rad num := by
      convert add_mem hL hq using 1; abel
    exact bil_congr _ hs hd hd
  · intro p S hpS ih hS L Q E h
    obtain ⟨hp, Δ, EΔ, hΔ, hmove⟩ := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ p' ∈ S, p'.Prime ∧ Moves num G p' m (c p') (c' p') := fun p' hp' => hS p' (Finset.mem_insert_of_mem hp')
    have hRep : ∀ i, Rep p (L i) fun x => c p x i ^ m := fun i => ((h i).2.2.2 p (Finset.mem_insert_self p S)).1
    have hsum := hmove L hRep
    refine (ih hS' (fun i => (L i).tens (Δ i)) (fun i => (Q i).tens (Δ i).dual) (fun i => E i + -EΔ i)
      fun i => ?_).trans ?_
    · obtain ⟨hQ, hL, hE, hRp⟩ := h i
      obtain ⟨hΔc, hΔv, hΔe⟩ := hΔ i
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact ((GlobalTheory.T.divisor_of_tensor_section_add k X q (Q i) (Δ i).dual).1 (E i) (-EΔ i) hQ
          ((GlobalTheory.T.divisor_of_tensor_section_add k X q (Δ i) (Δ i)).1 (EΔ i) (EΔ i) hΔc hΔc).2).1
      · have h1 := R.1 (L i) (Δ i)
        have h2 := R.1 (Q i) (Δ i).dual
        have h3 := R.2.1 (Δ i)
        convert sub_mem (sub_mem (sub_mem hL h1) h2) h3 using 1; abel
      · intro x hx
        by_cases hpx : Ov p x
        · have e := ((hRp p (Finset.mem_insert_self p S)).2 x hpx).add (hΔe x hpx).neg
          rwa [mul_inv_cancel] at e
        · have e := (hE x fun p'' hp'' => by
            rcases Finset.mem_insert.1 hp'' with rfl | hp''
            exacts [hpx, hx p'' hp'']).add (hΔv x hpx).neg
          rwa [inv_one, mul_one] at e
      · intro p' hp'S
        obtain ⟨hRepp', hEp'⟩ := hRp p' (Finset.mem_insert_of_mem hp'S)
        have hp'p : p' ≠ p := fun e => hpS (e ▸ hp'S)
        have nov : ∀ x : X, Ov p' x → ¬ Ov p x := fun x h₁ h₂ =>
          not_ov_and_ov (hS p' (Finset.mem_insert_of_mem hp'S)).1 hp hp'p x h₁ h₂
        refine ⟨?_, fun x hx => ?_⟩
        · obtain ⟨ρ, hρ, hρe⟩ := hRepp'
          obtain ⟨r, hr, hrd, -⟩ := hΔc
          obtain ⟨s, hs', hsd⟩ := (GlobalTheory.T.divisor_of_tensor_section_add k X q (L i) (Δ i)).2 ρ hρ r hr
          refine ⟨s, hs', fun x hx => ?_⟩
          rw [hsd, hrd]
          have e := (hρe x hx).add (hΔv x (nov x hx))
          rwa [mul_one] at e
        · have e := (hEp' x hx).add (hΔv x (nov x hx)).neg
          rwa [inv_one, mul_one] at e
    · rw [← hsum]
      exact Finset.sum_congr rfl fun i _ => bil_congr _ hs (R.1 _ _) (R.1 _ _)

end GlobalTheory.LatChain
