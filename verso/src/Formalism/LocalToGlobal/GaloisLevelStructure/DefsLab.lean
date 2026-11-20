import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

noncomputable section

open Polynomial

namespace Formalism.L2.NG

section lab

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]

def TameVal (A : ValuationSubring Ω) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p) (σ : Ω ≃ₐ[E] Ω) (d : ℕ)
    (z : Formalism.CyclotomicNorms.Fbar p) : Prop :=
  ∀ y : Ω, y ^ (p ^ d - 1) = (p : Ω) → NT.redThrough A κ (σ y / y) = z

def labPol (teich : Formalism.CyclotomicNorms.Fbar p →* ℂ) (f : (ZMod p)[X]) (j : ℕ) : ℂ[X] :=
  ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x ^ j)).prod

def LevelOf (f : (ZMod p)[X]) (d : ℕ) : Prop := 0 < d ∧ ∀ x ∈ Formalism.CyclotomicNorms.rootsBar f, x ^ (p ^ d - 1) = 1

def IsLabelOf (A : ValuationSubring Ω) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar p)
    (teich : Formalism.CyclotomicNorms.Fbar p →* ℂ) (I : Set (Ω ≃ₐ[E] Ω)) (n : ℕ) (P : (Ω ≃ₐ[E] Ω) → ℂ[X]) (f : (ZMod p)[X]) : Prop :=
  f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 ∧
    ∀ σ ∈ I, ∀ d j, LevelOf f d → TameVal A κ σ d (ζ d ^ j) → P σ = labPol teich f j

/- English proof (translation)
Simplify using `[labPol]`.
-/
theorem labPol_one (teich : Formalism.CyclotomicNorms.Fbar p →* ℂ) (f : (ZMod p)[X]) :
    labPol teich f 1 = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x)).prod := by
  simp [labPol]

/- English proof (translation)
Establish `hint : IsIntegral (ZMod p) x` using `(Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Set `K` to `IntermediateField.adjoin (ZMod p) {x}`. Establish `: FiniteDimensional (ZMod p) K` using `IntermediateField.adjoin.finiteDimensional hint`. Establish `: Finite K` using `Module.finite_of_finite (ZMod p)`. Establish `: Fintype K` using `Fintype.ofFinite K`.

Establish `hxK : x ∈ K` using `IntermediateField.mem_adjoin_simple_self (ZMod p) x`. Take `⟨d, _, hd⟩` from `FiniteField.card K p`. Use `⟨d, d.pos, ?_⟩` and prove the remaining obligations. Establish `h0 : (⟨x, hxK⟩ : K) ≠ 0` using `fun h => hx (congrArg Subtype.val h)`. Establish `h1` using `FiniteField.pow_card_sub_one_eq_one (⟨x, hxK⟩ : K) h0`.

Rewrite `h1` using `[hd]`. Conclude with `congrArg Subtype.val h1`.
-/
theorem exists_level_elt (x : Formalism.CyclotomicNorms.Fbar p) (hx : x ≠ 0) : ∃ d, 0 < d ∧ x ^ (p ^ d - 1) = 1 := by
  have hint : IsIntegral (ZMod p) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let K := IntermediateField.adjoin (ZMod p) {x}
  have : FiniteDimensional (ZMod p) K := IntermediateField.adjoin.finiteDimensional hint
  have : Finite K := Module.finite_of_finite (ZMod p)
  have : Fintype K := Fintype.ofFinite K
  have hxK : x ∈ K := IntermediateField.mem_adjoin_simple_self (ZMod p) x
  obtain ⟨d, _, hd⟩ := FiniteField.card K p
  refine ⟨d, d.pos, ?_⟩
  have h0 : (⟨x, hxK⟩ : K) ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one (⟨x, hxK⟩ : K) h0
  rw [hd] at h1
  exact congrArg Subtype.val h1

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : (p ^ d - 1) ∣ (p ^ (d * e) - 1) := by`. Rewrite using `[pow_mul]`. Conclude with `Nat.sub_one_dvd_pow_sub_one _ _`. Rewrite using `[hc, pow_mul, h, one_pow]`.
-/
theorem pow_level_mul {x : Formalism.CyclotomicNorms.Fbar p} {d : ℕ} (h : x ^ (p ^ d - 1) = 1) (e : ℕ) : x ^ (p ^ (d * e) - 1) = 1 := by
  obtain ⟨c, hc⟩ : (p ^ d - 1) ∣ (p ^ (d * e) - 1) := by
    rw [pow_mul]; exact Nat.sub_one_dvd_pow_sub_one _ _
  rw [hc, pow_mul, h, one_pow]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => exact ⟨1, one_pos, by simp⟩`. Consider the case `cons a s ih`. Take `⟨d, hd, h⟩` from `ih (fun h => hs (Multiset.mem_cons_of_mem h))`. Take `⟨e, he, h'⟩` from `exists_level_elt a (fun h => hs (h ▸ Multiset.mem_cons_self a s))`.

Use `⟨d * e, Nat.mul_pos hd he, fun x hx => ?_⟩` and prove the remaining obligations. Break down `Multiset.mem_cons.mp hx with rfl | hx` into its components or cases. Rewrite using `[mul_comm]`. Conclude with `pow_level_mul h' d`. Conclude with `pow_level_mul (h x hx) e`.
-/
theorem exists_level_multiset (s : Multiset (Formalism.CyclotomicNorms.Fbar p)) (hs : (0 : Formalism.CyclotomicNorms.Fbar p) ∉ s) :
    ∃ d, 0 < d ∧ ∀ x ∈ s, x ^ (p ^ d - 1) = 1 := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | cons a s ih =>
    obtain ⟨d, hd, h⟩ := ih (fun h => hs (Multiset.mem_cons_of_mem h))
    obtain ⟨e, he, h'⟩ := exists_level_elt a (fun h => hs (h ▸ Multiset.mem_cons_self a s))
    refine ⟨d * e, Nat.mul_pos hd he, fun x hx => ?_⟩
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · rw [mul_comm]; exact pow_level_mul h' d
    · exact pow_level_mul (h x hx) e

/- English proof (translation)
Apply `exists_level_multiset` to reduce the goal to its premises. Introduce `h`. Establish `h1` using `(Polynomial.mem_roots'.mp h).2`. Rewrite `h1` using `[IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map]`. Conclude with `h0 ((map_eq_zero _).mp h1)`.
-/
theorem exists_level (f : (ZMod p)[X]) (h0 : f.coeff 0 ≠ 0) : ∃ d, LevelOf f d := by
  apply exists_level_multiset
  intro h
  have h1 := (Polynomial.mem_roots'.mp h).2
  rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map] at h1
  exact h0 ((map_eq_zero _).mp h1)

variable {A : ValuationSubring Ω} {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {ζ : ℕ → Formalism.CyclotomicNorms.Fbar p}
  {teich : Formalism.CyclotomicNorms.Fbar p →* ℂ} {I : Set (Ω ≃ₐ[E] Ω)} {n : ℕ} {P : (Ω ≃ₐ[E] Ω) → ℂ[X]} {f f' : (ZMod p)[X]}

/- English proof (translation)
Take `⟨d, hd⟩` from `exists_level f h.2.2.1`. Rewrite using `[← labPol_one]`. Conclude with `h.2.2.2 σ hσ d 1 hd (by rw [pow_one]; exact hc d hd.1)`.
-/
theorem IsLabelOf.at_gen (h : IsLabelOf A κ ζ teich I n P f) {σ : Ω ≃ₐ[E] Ω} (hσ : σ ∈ I) (hc : NT.TameCoupled A κ σ ζ) :
    P σ = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x)).prod := by
  obtain ⟨d, hd⟩ := exists_level f h.2.2.1
  rw [← labPol_one]
  exact h.2.2.2 σ hσ d 1 hd (by rw [pow_one]; exact hc d hd.1)

/- English proof (translation)
Establish `e1` using `(IsAlgClosed.splits (f.map (algebraMap (ZMod p) (Formalism.CyclotomicNorms.Fbar p)))).eq_prod_roots_of_monic (hf.map _)`. Establish `e2` using `(IsAlgClosed.splits (f'.map (algebraMap (ZMod p) (Formalism.CyclotomicNorms.Fbar p)))).eq_prod_roots_of_monic (hf'.map _)`. Unfold `Formalism.CyclotomicNorms.rootsBar at h`. Rewrite `e1` using `[h, ← e2]`. Conclude with `Polynomial.map_injective _ (algebraMap (ZMod p) (Formalism.CyclotomicNorms.Fbar p)).injective e1`.
-/
theorem eq_of_rootsBar_eq (hf : f.Monic) (hf' : f'.Monic) (h : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar f') : f = f' := by
  have e1 := (IsAlgClosed.splits (f.map (algebraMap (ZMod p) (Formalism.CyclotomicNorms.Fbar p)))).eq_prod_roots_of_monic (hf.map _)
  have e2 := (IsAlgClosed.splits (f'.map (algebraMap (ZMod p) (Formalism.CyclotomicNorms.Fbar p)))).eq_prod_roots_of_monic (hf'.map _)
  unfold Formalism.CyclotomicNorms.rootsBar at h
  rw [h, ← e2] at e1
  exact Polynomial.map_injective _ (algebraMap (ZMod p) (Formalism.CyclotomicNorms.Fbar p)).injective e1

/- English proof (translation)
Establish `e` using `(h.at_gen hσ hc).symm.trans (h'.at_gen hσ hc)`. Establish `r` using `congrArg Polynomial.roots e`. Establish `key : ∀ s : Multiset (Formalism.CyclotomicNorms.Fbar p), ((s.map fun x => X - C (teich x)).prod).roots = s.map teich`. Introduce `s`. Establish `: (s.map fun x => X - C (teich x)) = (s.map teich).map fun a => X - C a` using `by rw [Multiset.map_map]; rfl`.

Rewrite using `[this, Polynomial.roots_multiset_prod_X_sub_C]`. Rewrite `r` using `[key, key]`. Conclude with `eq_of_rootsBar_eq h.1 h'.1 (Multiset.map_injective ht r)`.
-/
theorem IsLabelOf.unique (h : IsLabelOf A κ ζ teich I n P f) (h' : IsLabelOf A κ ζ teich I n P f')
    (ht : Function.Injective teich) {σ : Ω ≃ₐ[E] Ω} (hσ : σ ∈ I) (hc : NT.TameCoupled A κ σ ζ) : f = f' := by
  have e := (h.at_gen hσ hc).symm.trans (h'.at_gen hσ hc)
  have r := congrArg Polynomial.roots e
  have key : ∀ s : Multiset (Formalism.CyclotomicNorms.Fbar p), ((s.map fun x => X - C (teich x)).prod).roots = s.map teich := by
    intro s
    have : (s.map fun x => X - C (teich x)) = (s.map teich).map fun a => X - C a := by rw [Multiset.map_map]; rfl
    rw [this, Polynomial.roots_multiset_prod_X_sub_C]
  rw [key, key] at r
  exact eq_of_rootsBar_eq h.1 h'.1 (Multiset.map_injective ht r)

end lab

end Formalism.L2.NG
