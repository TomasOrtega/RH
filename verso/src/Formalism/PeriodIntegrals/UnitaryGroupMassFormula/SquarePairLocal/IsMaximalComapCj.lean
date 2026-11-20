import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOfSteps

noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

def Dv (Q : Ideal (𝓞 E)) (c x : 𝓞 E) : Prop :=
  ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = c * w

section Pres

variable {L : Submodule (𝓞 E) (Fin N → E)}

/- English proof (translation)
Introduce `y _`. Rewrite using `[Matrix.zero_mulVec]`. Conclude with `L.zero_mem`.
-/
theorem pres_zero : Pres L (0 : Matrix (Fin N) (Fin N) E) := by
  intro y _
  rw [Matrix.zero_mulVec]
  exact L.zero_mem

/- English proof (translation)
Introduce `y hy`. Rewrite using `[Matrix.add_mulVec]`. Conclude with `L.add_mem (he y hy) (hf y hy)`.
-/
theorem pres_add {e f : Matrix (Fin N) (Fin N) E} (he : Pres L e) (hf : Pres L f) :
    Pres L (e + f) := by
  intro y hy
  rw [Matrix.add_mulVec]
  exact L.add_mem (he y hy) (hf y hy)

/- English proof (translation)
Introduce `y hy`. Rewrite using `[Matrix.sub_mulVec]`. Conclude with `L.sub_mem (he y hy) (hf y hy)`.
-/
theorem pres_sub {e f : Matrix (Fin N) (Fin N) E} (he : Pres L e) (hf : Pres L f) :
    Pres L (e - f) := by
  intro y hy
  rw [Matrix.sub_mulVec]
  exact L.sub_mem (he y hy) (hf y hy)

/- English proof (translation)
Introduce `y hy`. Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `he _ (hf y hy)`.
-/
theorem pres_mul {e f : Matrix (Fin N) (Fin N) E} (he : Pres L e) (hf : Pres L f) :
    Pres L (e * f) := by
  intro y hy
  rw [← Matrix.mulVec_mulVec]
  exact he _ (hf y hy)

/- English proof (translation)
Use `first`. Consider the case `exact (algebraMap_smul E r v).symm`. Consider the case `rfl`. Consider the case `(ext i; simp [Algebra.smul_def])`.
-/
private lemma integers_smul_eq_coe_smul (r : 𝓞 E) (v : Fin N → E) : r • v = (r : E) • v := by
  first
    | exact (algebraMap_smul E r v).symm
    | rfl
    | (ext i; simp [Algebra.smul_def])

/- English proof (translation)
Use `first`. Consider the case `exact Matrix.smul_mulVec a A b`. Consider the case `exact Matrix.smul_mulVec_assoc a A b`. Consider the case `(ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])`.
-/
private lemma smul_mulVec_eq_smul (a : E) (A : Matrix (Fin N) (Fin N) E) (b : Fin N → E) :
    (a • A) *ᵥ b = a • (A *ᵥ b) := by
  first
    | exact Matrix.smul_mulVec a A b
    | exact Matrix.smul_mulVec_assoc a A b
    | (ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])

/- English proof (translation)
Introduce `y hy`. Rewrite using `[smul_mulVec_eq_smul, ← integers_smul_eq_coe_smul]`. Conclude with `L.smul_mem r (he y hy)`.
-/
theorem pres_smul (r : 𝓞 E) {e : Matrix (Fin N) (Fin N) E} (he : Pres L e) :
    Pres L ((r : E) • e) := by
  intro y hy
  rw [smul_mulVec_eq_smul, ← integers_smul_eq_coe_smul]
  exact L.smul_mem r (he y hy)

/- English proof (translation)
Use `first`. Consider the case `simp only [stdHG, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']`. Consider the case `simp only [stdHG, Matrix.mulVec, Matrix.dotProduct, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem stdHG_conj (e : Matrix (Fin N) (Fin N) E) (x y : Fin N → E) :
    stdHG E N x (eᴴ *ᵥ y) = stdHG E N (e *ᵥ x) y := by
  first
    | simp only [stdHG, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Finset.mul_sum,
        Finset.sum_mul, star_sum, star_mul']
    | simp only [stdHG, Matrix.mulVec, Matrix.dotProduct, Matrix.conjTranspose_apply,
        Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `hmem : ∀ y, y ∈ L ↔ ∀ x ∈ L, stdHG E N x y ∈ (algebraMap (𝓞 E) E).range` using `by first`. Consider the case `exact hL.2.2`. Consider the case `(unfold IsSDG at hL; exact hL.2.2)`. Introduce `y hy`. Use `(hmem _).2 fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[stdHG_conj]`. Conclude with `(hmem y).1 hy _ (he x hx)`.
-/
theorem pres_conj (hL : IsSDG E N L) {e : Matrix (Fin N) (Fin N) E} (he : Pres L e) :
    Pres L eᴴ := by
  have hmem : ∀ y, y ∈ L ↔ ∀ x ∈ L, stdHG E N x y ∈ (algebraMap (𝓞 E) E).range := by
    first
      | exact hL.2.2
      | (unfold IsSDG at hL; exact hL.2.2)
  intro y hy
  refine (hmem _).2 fun x hx => ?_
  rw [stdHG_conj]
  exact (hmem y).1 hy _ (he x hx)

end Pres

section Cj

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_cj (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl

/- English proof (translation)
Establish `h : ((cj E (cj E x) : 𝓞 E) : E) = (x : E)` using `by rw [coe_cj, coe_cj, star_star]`. Use `first`. Consider the case `exact_mod_cast h`. Consider the case `exact RingOfIntegers.ext h`. Consider the case `exact Subtype.ext h`.
-/
theorem cj_cj (x : 𝓞 E) : cj E (cj E x) = x := by
  have h : ((cj E (cj E x) : 𝓞 E) : E) = (x : E) := by rw [coe_cj, coe_cj, star_star]
  first
    | exact_mod_cast h
    | exact RingOfIntegers.ext h
    | exact Subtype.ext h

/- English proof (translation)
Introduce `x` and use `⟨cj E x, cj_cj x⟩`.
-/
theorem cj_surj : Function.Surjective (cj E) := fun x => ⟨cj E x, cj_cj x⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Ideal.mem_comap, cj_cj]`.
-/
theorem comap_cj_comap (I : Ideal (𝓞 E)) : (I.comap (cj E)).comap (cj E) = I := by
  ext x
  simp only [Ideal.mem_comap, cj_cj]

/- English proof (translation)
Use `haveI := hQ`. Conclude with `Ideal.comap_isMaximal_of_surjective (cj E) cj_surj`.
-/
theorem isMaximal_comap_cj {Q : Ideal (𝓞 E)} (hQ : Q.IsMaximal) : (Q.comap (cj E)).IsMaximal := by
  haveI := hQ
  exact Ideal.comap_isMaximal_of_surjective (cj E) cj_surj

/- English proof (translation)
Establish `h'` using `Ideal.le_comap_pow (cj E) K h`. Use `first`. Consider the case `exact Ideal.mem_comap.mp h'`. Consider the case `exact h'`.
-/
theorem cj_mem_pow {I : Ideal (𝓞 E)} {K : ℕ} {x : 𝓞 E} (h : x ∈ (I.comap (cj E)) ^ K) :
    cj E x ∈ I ^ K := by
  have h' := Ideal.le_comap_pow (cj E) K h
  first
    | exact Ideal.mem_comap.mp h'
    | exact h'

/- English proof (translation)
Use `first`. Consider the case `exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField E)`. Consider the case `exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField E)`.
-/
theorem ne_bot_of_max {Q : Ideal (𝓞 E)} (hQ : Q.IsMaximal) : Q ≠ ⊥ := by
  first
    | exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField E)
    | exact Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField E)

end Cj

/- English proof (translation)
Establish `h1 : ∀ P ∈ S, ∃ K : ℕ, ∀ x ∈ P ^ K, Dv P c x` using `fun P hPS => hP E P (hS P hPS) c hc`. Use `choose! Kf hKf using h1`. Conclude with `⟨S.sup Kf, fun P hPS x hx => hKf P hPS x (Ideal.pow_le_pow_right (Finset.le_sup hPS) hx)⟩`.
-/
theorem powLoc_fin (hP : PowLoc) (S : Finset (Ideal (𝓞 E))) (hS : ∀ P ∈ S, P.IsMaximal)
    {c : 𝓞 E} (hc : c ≠ 0) : ∃ K : ℕ, ∀ P ∈ S, ∀ x ∈ P ^ K, Dv P c x := by
  classical
  have h1 : ∀ P ∈ S, ∃ K : ℕ, ∀ x ∈ P ^ K, Dv P c x := fun P hPS => hP E P (hS P hPS) c hc
  choose! Kf hKf using h1
  exact ⟨S.sup Kf, fun P hPS x hx =>
    hKf P hPS x (Ideal.pow_le_pow_right (Finset.le_sup hPS) hx)⟩

section Small

variable {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}

/- English proof (translation)
Introduce `y hy`. Take `⟨s, hs, w, hw⟩` from `hρ`. Use `⟨s, hs, w • (X *ᵥ y), L.smul_mem w (hX y hy), ?_⟩` and prove the remaining obligations. Establish `hw' : (s : E) * (ρ : E) = (c : E) * (w : E)` using `by first`. Consider the case `exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hw`.

Consider the case `simpa using congrArg (fun t : 𝓞 E => (t : E)) hw`. Simplify using `only [integers_smul_eq_coe_smul]`. Rewrite using `[smul_mulVec_eq_smul, smul_smul, smul_smul, hw']`.
-/
theorem smallAt_smul {ρ : 𝓞 E} {X : Matrix (Fin N) (Fin N) E} (hρ : Dv Q c ρ) (hX : Pres L X) :
    SmallAt Q c L ((ρ : E) • X) := by
  intro y hy
  obtain ⟨s, hs, w, hw⟩ := hρ
  refine ⟨s, hs, w • (X *ᵥ y), L.smul_mem w (hX y hy), ?_⟩
  have hw' : (s : E) * (ρ : E) = (c : E) * (w : E) := by
    first
      | exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hw
      | simpa using congrArg (fun t : 𝓞 E => (t : E)) hw
  simp only [integers_smul_eq_coe_smul]
  rw [smul_mulVec_eq_smul, smul_smul, smul_smul, hw']

/- English proof (translation)
Introduce `y hy`. Take `⟨s, hs, m, hm, e1⟩` from `hA y hy`. Take `⟨t, ht, n, hn, e2⟩` from `hB y hy`. Use `⟨s * t, fun h => ?_, t • m + s • n, L.add_mem (L.smul_mem t hm) (L.smul_mem s hn), ?_⟩` and prove the remaining obligations. Break down `Ideal.IsPrime.mem_or_mem ‹Q.IsPrime› h with h | h` into its components or cases.

Conclude with `hs h`. Conclude with `ht h`. Establish `f1 : (s * t) • (A *ᵥ y) = c • (t • m)`. Rewrite using `[mul_comm, mul_smul, e1, smul_comm]`. Establish `f2 : (s * t) • (B *ᵥ y) = c • (s • n)`.

Rewrite using `[mul_smul, e2, smul_comm]`. Rewrite using `[Matrix.add_mulVec, smul_add, smul_add, f1, f2]`.
-/
private lemma smallAt_add' {A B : Matrix (Fin N) (Fin N) E} (hA : SmallAt Q c L A)
    (hB : SmallAt Q c L B) : SmallAt Q c L (A + B) := by
  intro y hy
  obtain ⟨s, hs, m, hm, e1⟩ := hA y hy
  obtain ⟨t, ht, n, hn, e2⟩ := hB y hy
  refine ⟨s * t, fun h => ?_, t • m + s • n, L.add_mem (L.smul_mem t hm) (L.smul_mem s hn), ?_⟩
  · rcases Ideal.IsPrime.mem_or_mem ‹Q.IsPrime› h with h | h
    · exact hs h
    · exact ht h
  · have f1 : (s * t) • (A *ᵥ y) = c • (t • m) := by
      rw [mul_comm, mul_smul, e1, smul_comm]
    have f2 : (s * t) • (B *ᵥ y) = c • (s • n) := by
      rw [mul_smul, e2, smul_comm]
    rw [Matrix.add_mulVec, smul_add, smul_add, f1, f2]

/- English proof (translation)
Establish `k1 : (e₀ + (ρ : E) • D) * (e₀ + (ρ : E) • D) - (e₀ + (ρ : E) • D) = (e₀ * e₀ - e₀) + (ρ : E) • (e₀ * D + D * e₀ - D + (ρ : E) • (D * D))`. Simplify using `only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `k2 : (e₀ + (ρ : E) • D) + (e₀ + (ρ : E) • D)ᴴ - 1 = (e₀ + e₀ᴴ - 1) + (ρ : E) • D + ((cj E ρ : 𝓞 E) : E) • Dᴴ`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, coe_cj]`.

Normalize the expressions using the abelian group laws. Establish `pD : Pres L (e₀ * D + D * e₀ - D + (ρ : E) • (D * D))` using `pres_add (pres_sub (pres_add (pres_mul h₀ hD) (pres_mul hD h₀)) hD) (pres_smul ρ (pres_mul hD hD))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[k1]`. Conclude with `smallAt_add' g1 (smallAt_smul hρ pD)`.

Rewrite using `[k2]`. Conclude with `smallAt_add' (smallAt_add' g2 (smallAt_smul hρ hD)) (smallAt_smul hρc (pres_conj hL hD))`.
-/
theorem small_pert (hL : IsSDG E N L) {e₀ D : Matrix (Fin N) (Fin N) E} {ρ : 𝓞 E}
    (h₀ : Pres L e₀) (hD : Pres L D) (hρ : Dv Q c ρ) (hρc : Dv Q c (cj E ρ))
    (g1 : SmallAt Q c L (e₀ * e₀ - e₀)) (g2 : SmallAt Q c L (e₀ + e₀ᴴ - 1)) :
    SmallAt Q c L ((e₀ + (ρ : E) • D) * (e₀ + (ρ : E) • D) - (e₀ + (ρ : E) • D)) ∧
      SmallAt Q c L ((e₀ + (ρ : E) • D) + (e₀ + (ρ : E) • D)ᴴ - 1) := by
  have k1 : (e₀ + (ρ : E) • D) * (e₀ + (ρ : E) • D) - (e₀ + (ρ : E) • D) =
      (e₀ * e₀ - e₀) + (ρ : E) • (e₀ * D + D * e₀ - D + (ρ : E) • (D * D)) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]
    abel
  have k2 : (e₀ + (ρ : E) • D) + (e₀ + (ρ : E) • D)ᴴ - 1 =
      (e₀ + e₀ᴴ - 1) + (ρ : E) • D + ((cj E ρ : 𝓞 E) : E) • Dᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, coe_cj]
    abel
  have pD : Pres L (e₀ * D + D * e₀ - D + (ρ : E) • (D * D)) :=
    pres_add (pres_sub (pres_add (pres_mul h₀ hD) (pres_mul hD h₀)) hD)
      (pres_smul ρ (pres_mul hD hD))
  refine ⟨?_, ?_⟩
  · rw [k1]
    exact smallAt_add' g1 (smallAt_smul hρ pD)
  · rw [k2]
    exact smallAt_add' (smallAt_add' g2 (smallAt_smul hρ hD))
      (smallAt_smul hρc (pres_conj hL hD))

/- English proof (translation)
Take `⟨a, b, c2, d⟩` from `hg`. Take `⟨x1, x2⟩` from `small_pert h' h₀' hD' hρ hρc a c2`. Take `⟨y1, y2⟩` from `small_pert h'' h₀'' hD'' hρ hρc b d`. Use `first`. Consider the case `exact ⟨x1, y1, x2, y2⟩`.

Consider the case `(unfold Good; exact ⟨x1, y1, x2, y2⟩)`.
-/
theorem good_pert {L' L'' : Submodule (𝓞 E) (Fin N → E)} (h' : IsSDG E N L') (h'' : IsSDG E N L'')
    {e₀ D : Matrix (Fin N) (Fin N) E} {ρ : 𝓞 E} (hg : Good Q c L' L'' e₀)
    (h₀' : Pres L' e₀) (h₀'' : Pres L'' e₀) (hD' : Pres L' D) (hD'' : Pres L'' D)
    (hρ : Dv Q c ρ) (hρc : Dv Q c (cj E ρ)) : Good Q c L' L'' (e₀ + (ρ : E) • D) := by
  obtain ⟨a, b, c2, d⟩ := hg
  obtain ⟨x1, x2⟩ := small_pert h' h₀' hD' hρ hρc a c2
  obtain ⟨y1, y2⟩ := small_pert h'' h₀'' hD'' hρ hρc b d
  first
    | exact ⟨x1, y1, x2, y2⟩
    | (unfold Good; exact ⟨x1, y1, x2, y2⟩)

end Small

/- English proof (translation)
Take `⟨K, hK⟩` from `powLoc_fin hP (A ∪ B) (fun P h => (Finset.mem_union.mp h).elim (hAm P) (hBm P)) hc`. Establish `hcop : IsCoprime (∏ P ∈ A, P ^ K) (∏ P ∈ B \ A, P ^ K)`. Use `IsCoprime.prod_left fun P hPA => IsCoprime.prod_right fun P' hP' => ?_` and prove the remaining obligations. Establish `hne : P ≠ P'` using `fun h => (Finset.mem_sdiff.mp hP').2 (h ▸ hPA)`. Conclude with `(Ideal.isCoprime_iff_sup_eq.mpr ((hAm P hPA).coprime_of_ne (hBm P' (Finset.mem_sdiff.mp hP').1) hne)).pow`.

Establish `h1 : (1 : 𝓞 E) ∈ (∏ P ∈ A, P ^ K) ⊔ ∏ P ∈ B \ A, P ^ K`. Rewrite using `[Ideal.isCoprime_iff_sup_eq.mp hcop]`. Conclude with `Submodule.mem_top`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp h1`. Establish `memA : ∀ P ∈ A, a ∈ P ^ K` using `fun P h => by first`.

Consider the case `exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun Q => Q ^ K) h) ha`. Consider the case `exact Ideal.prod_le_inf.trans (Finset.inf_le h) ha`. Establish `memB : ∀ P ∈ B \ A, b ∈ P ^ K` using `fun P h => by first`. Consider the case `exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun Q => Q ^ K) h) hb`. Consider the case `exact Ideal.prod_le_inf.trans (Finset.inf_le h) hb`.

Establish `hab' : (a : E) + (b : E) = 1` using `by exact_mod_cast hab`. Establish `hnb : ((-b : 𝓞 E) : E) = -(b : E)` using `by first`. Consider the case `rfl`. Consider the case `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `simp`. Establish `heq : e₁ + (a : E) • (e₂ - e₁) = e₂ + ((-b : 𝓞 E) : E) • (e₂ - e₁)`. Rewrite using `[hnb, eq_sub_of_add_eq hab', sub_smul, one_smul, neg_smul]`. Normalize the expressions using the abelian group laws. Use `⟨e₁ + (a : E) • (e₂ - e₁), pres_add p₁' (pres_smul a (pres_sub p₂' p₁')), pres_add p₁'' (pres_smul a (pres_sub p₂'' p₁'')), fun P hPU => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hPA : P ∈ A`. Use `haveI := (hAm P hPA).isPrime`. Conclude with `good_pert h' h'' (g₁ P hPA) p₁' p₁'' (pres_sub p₂' p₁') (pres_sub p₂'' p₁'') (hK P (Finset.mem_union_left _ hPA) a (memA P hPA)) (hK P (Finset.mem_union_left _ hPA) _ (cj_mem_pow (memA _ (hA P hPA))))`. Establish `hPB : P ∈ B` using `(Finset.mem_union.mp hPU).resolve_left hPA`. Establish `hPBA : P ∈ B \ A` using `Finset.mem_sdiff.mpr ⟨hPB, hPA⟩`.

Establish `hcB : P.comap (cj E) ∈ B \ A`. Use `Finset.mem_sdiff.mpr ⟨hB P hPB, fun h => hPA ?_⟩` and prove the remaining obligations. Establish `h2` using `hA _ h`. Rewrite `h2` using `[comap_cj_comap]`. Then use the resulting hypothesis. Use `haveI := (hBm P hPB).isPrime`.

Rewrite using `[heq]`. Conclude with `good_pert h' h'' (g₂ P hPB) p₂' p₂'' (pres_sub p₂' p₁') (pres_sub p₂'' p₁'') (hK P (Finset.mem_union_right _ hPB) _ (neg_mem (memB P hPBA))) (hK P (Finset.mem_union_right _ hPB) _ (cj_mem_pow (neg_mem (memB _ hcB))))`.
-/
theorem glue_two (hP : PowLoc) {L' L'' : Submodule (𝓞 E) (Fin N → E)} (h' : IsSDG E N L')
    (h'' : IsSDG E N L'') {c : 𝓞 E} (hc : c ≠ 0) (A B : Finset (Ideal (𝓞 E)))
    (hAm : ∀ P ∈ A, P.IsMaximal) (hBm : ∀ P ∈ B, P.IsMaximal)
    (hA : ∀ P ∈ A, P.comap (cj E) ∈ A) (hB : ∀ P ∈ B, P.comap (cj E) ∈ B)
    {e₁ e₂ : Matrix (Fin N) (Fin N) E} (p₁' : Pres L' e₁) (p₁'' : Pres L'' e₁)
    (p₂' : Pres L' e₂) (p₂'' : Pres L'' e₂)
    (g₁ : ∀ P ∈ A, Good P c L' L'' e₁) (g₂ : ∀ P ∈ B, Good P c L' L'' e₂) :
    ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧ ∀ P ∈ A ∪ B, Good P c L' L'' e := by
  classical
  obtain ⟨K, hK⟩ := powLoc_fin hP (A ∪ B)
    (fun P h => (Finset.mem_union.mp h).elim (hAm P) (hBm P)) hc
  have hcop : IsCoprime (∏ P ∈ A, P ^ K) (∏ P ∈ B \ A, P ^ K) := by
    refine IsCoprime.prod_left fun P hPA => IsCoprime.prod_right fun P' hP' => ?_
    have hne : P ≠ P' := fun h => (Finset.mem_sdiff.mp hP').2 (h ▸ hPA)
    exact (Ideal.isCoprime_iff_sup_eq.mpr
      ((hAm P hPA).coprime_of_ne (hBm P' (Finset.mem_sdiff.mp hP').1) hne)).pow
  have h1 : (1 : 𝓞 E) ∈ (∏ P ∈ A, P ^ K) ⊔ ∏ P ∈ B \ A, P ^ K := by
    rw [Ideal.isCoprime_iff_sup_eq.mp hcop]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  have memA : ∀ P ∈ A, a ∈ P ^ K := fun P h => by
    first
      | exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun Q => Q ^ K) h) ha
      | exact Ideal.prod_le_inf.trans (Finset.inf_le h) ha
  have memB : ∀ P ∈ B \ A, b ∈ P ^ K := fun P h => by
    first
      | exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun Q => Q ^ K) h) hb
      | exact Ideal.prod_le_inf.trans (Finset.inf_le h) hb
  have hab' : (a : E) + (b : E) = 1 := by exact_mod_cast hab
  have hnb : ((-b : 𝓞 E) : E) = -(b : E) := by
    first
      | rfl
      | push_cast; ring
      | simp
  have heq : e₁ + (a : E) • (e₂ - e₁) = e₂ + ((-b : 𝓞 E) : E) • (e₂ - e₁) := by
    rw [hnb, eq_sub_of_add_eq hab', sub_smul, one_smul, neg_smul]
    abel
  refine ⟨e₁ + (a : E) • (e₂ - e₁), pres_add p₁' (pres_smul a (pres_sub p₂' p₁')),
    pres_add p₁'' (pres_smul a (pres_sub p₂'' p₁'')), fun P hPU => ?_⟩
  by_cases hPA : P ∈ A
  · haveI := (hAm P hPA).isPrime
    exact good_pert h' h'' (g₁ P hPA) p₁' p₁'' (pres_sub p₂' p₁') (pres_sub p₂'' p₁'')
      (hK P (Finset.mem_union_left _ hPA) a (memA P hPA))
      (hK P (Finset.mem_union_left _ hPA) _ (cj_mem_pow (memA _ (hA P hPA))))
  · have hPB : P ∈ B := (Finset.mem_union.mp hPU).resolve_left hPA
    have hPBA : P ∈ B \ A := Finset.mem_sdiff.mpr ⟨hPB, hPA⟩
    have hcB : P.comap (cj E) ∈ B \ A := by
      refine Finset.mem_sdiff.mpr ⟨hB P hPB, fun h => hPA ?_⟩
      have h2 := hA _ h
      rwa [comap_cj_comap] at h2
    haveI := (hBm P hPB).isPrime
    rw [heq]
    exact good_pert h' h'' (g₂ P hPB) p₂' p₂'' (pres_sub p₂' p₁') (pres_sub p₂'' p₁'')
      (hK P (Finset.mem_union_right _ hPB) _ (neg_mem (memB P hPBA)))
      (hK P (Finset.mem_union_right _ hPB) _ (cj_mem_pow (neg_mem (memB _ hcB))))

/- English proof (translation)
Use `revert hT`. Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Introduce `_`. Conclude with `⟨0, pres_zero, pres_zero, fun P h => by simp at h⟩`. Introduce `Q T' _ ih hT`.

Take `⟨e₁, p₁', p₁'', g₁⟩` from `ih (fun P hP' => hT P (Finset.mem_insert_of_mem hP'))`. Establish `hQm : Q.IsMaximal` using `hT Q (Finset.mem_insert_self Q T')`. Take `⟨e₂, p₂', p₂'', gQ, gQc⟩` from `hO E hE N L' L'' hN h' h'' Q hQm c hc`. Establish `hAm : ∀ P ∈ T' ∪ T'.image (fun P => P.comap (cj E)), P.IsMaximal`. Introduce `P hP'`.

Break down `Finset.mem_union.mp hP' with h | h` into its components or cases. Conclude with `hT P (Finset.mem_insert_of_mem h)`. Take `⟨P0, hP0, rfl⟩` from `Finset.mem_image.mp h`. Conclude with `isMaximal_comap_cj (hT P0 (Finset.mem_insert_of_mem hP0))`. Establish `hBm : ∀ P ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))), P.IsMaximal`.

Introduce `P hP'`. Break down `Finset.mem_insert.mp hP' with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `hQm`. Rewrite using `[Finset.mem_singleton.mp h]`.

Conclude with `isMaximal_comap_cj hQm`. Establish `hA : ∀ P ∈ T' ∪ T'.image (fun P => P.comap (cj E)), P.comap (cj E) ∈ T' ∪ T'.image (fun P => P.comap (cj E))`. Introduce `P hP'`. Break down `Finset.mem_union.mp hP' with h | h` into its components or cases. Conclude with `Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)`.

Take `⟨P0, hP0, rfl⟩` from `Finset.mem_image.mp h`. Simplify using `only [comap_cj_comap]`. Conclude with `Finset.mem_union_left _ hP0`. Establish `hB : ∀ P ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))), P.comap (cj E) ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E)))`. Introduce `P hP'`.

Break down `Finset.mem_insert.mp hP' with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `Finset.mem_insert_of_mem (Finset.mem_singleton_self _)`. Rewrite using `[Finset.mem_singleton.mp h, comap_cj_comap]`. Conclude with `Finset.mem_insert_self _ _`.

Establish `hg₁ : ∀ P ∈ T' ∪ T'.image (fun P => P.comap (cj E)), Good P c L' L'' e₁`. Introduce `P hP'`. Break down `Finset.mem_union.mp hP' with h | h` into its components or cases. Conclude with `(g₁ P h).1`. Take `⟨P0, hP0, rfl⟩` from `Finset.mem_image.mp h`.

Conclude with `(g₁ P0 hP0).2`. Establish `hg₂ : ∀ P ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))), Good P c L' L'' e₂`. Introduce `P hP'`. Break down `Finset.mem_insert.mp hP' with h | h` into its components or cases. Rewrite using `[h]`.

Conclude with `gQ`. Rewrite using `[Finset.mem_singleton.mp h]`. Conclude with `gQc`. Take `⟨e, q', q'', g⟩` from `glue_two hP h' h'' hc _ _ hAm hBm hA hB p₁' p₁'' p₂' p₂'' hg₁ hg₂`. Use `⟨e, q', q'', fun P hP' => ?_⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.mp hP' with h | hPT` into its components or cases. Rewrite using `[h]`. Conclude with `⟨g _ (Finset.mem_union_right _ (Finset.mem_insert_self _ _)), g _ (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))⟩`. Conclude with `⟨g _ (Finset.mem_union_left _ (Finset.mem_union_left _ hPT)), g _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPT)))⟩`.
-/
theorem glue_fin (hP : PowLoc) (hO : OnePlace) (hE : PI.IsCMUnram E)
    {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hN : Even N) (h' : IsSDG E N L') (h'' : IsSDG E N L'')
    {c : 𝓞 E} (hc : c ≠ 0) (T : Finset (Ideal (𝓞 E))) (hT : ∀ P ∈ T, P.IsMaximal) :
    ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧
      ∀ P ∈ T, Good P c L' L'' e ∧ Good (P.comap (cj E)) c L' L'' e := by
  classical
  revert hT
  refine Finset.induction_on T ?_ ?_
  · intro _
    exact ⟨0, pres_zero, pres_zero, fun P h => by simp at h⟩
  · intro Q T' _ ih hT
    obtain ⟨e₁, p₁', p₁'', g₁⟩ := ih (fun P hP' => hT P (Finset.mem_insert_of_mem hP'))
    have hQm : Q.IsMaximal := hT Q (Finset.mem_insert_self Q T')
    obtain ⟨e₂, p₂', p₂'', gQ, gQc⟩ := hO E hE N L' L'' hN h' h'' Q hQm c hc
    have hAm : ∀ P ∈ T' ∪ T'.image (fun P => P.comap (cj E)), P.IsMaximal := by
      intro P hP'
      rcases Finset.mem_union.mp hP' with h | h
      · exact hT P (Finset.mem_insert_of_mem h)
      · obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp h
        exact isMaximal_comap_cj (hT P0 (Finset.mem_insert_of_mem hP0))
    have hBm : ∀ P ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))), P.IsMaximal := by
      intro P hP'
      rcases Finset.mem_insert.mp hP' with h | h
      · rw [h]; exact hQm
      · rw [Finset.mem_singleton.mp h]; exact isMaximal_comap_cj hQm
    have hA : ∀ P ∈ T' ∪ T'.image (fun P => P.comap (cj E)),
        P.comap (cj E) ∈ T' ∪ T'.image (fun P => P.comap (cj E)) := by
      intro P hP'
      rcases Finset.mem_union.mp hP' with h | h
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
      · obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp h
        simp only [comap_cj_comap]
        exact Finset.mem_union_left _ hP0
    have hB : ∀ P ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))),
        P.comap (cj E) ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))) := by
      intro P hP'
      rcases Finset.mem_insert.mp hP' with h | h
      · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · rw [Finset.mem_singleton.mp h, comap_cj_comap]
        exact Finset.mem_insert_self _ _
    have hg₁ : ∀ P ∈ T' ∪ T'.image (fun P => P.comap (cj E)), Good P c L' L'' e₁ := by
      intro P hP'
      rcases Finset.mem_union.mp hP' with h | h
      · exact (g₁ P h).1
      · obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp h
        exact (g₁ P0 hP0).2
    have hg₂ : ∀ P ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))), Good P c L' L'' e₂ := by
      intro P hP'
      rcases Finset.mem_insert.mp hP' with h | h
      · rw [h]; exact gQ
      · rw [Finset.mem_singleton.mp h]; exact gQc
    obtain ⟨e, q', q'', g⟩ :=
      glue_two hP h' h'' hc _ _ hAm hBm hA hB p₁' p₁'' p₂' p₂'' hg₁ hg₂
    refine ⟨e, q', q'', fun P hP' => ?_⟩
    rcases Finset.mem_insert.mp hP' with h | hPT
    · rw [h]
      exact ⟨g _ (Finset.mem_union_right _ (Finset.mem_insert_self _ _)),
        g _ (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))⟩
    · exact ⟨g _ (Finset.mem_union_left _ (Finset.mem_union_left _ hPT)),
        g _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPT)))⟩

/- English proof (translation)
Introduce `hO E _ _ _ hE N L' L'' hN h' h'' p hp a`. Establish `hp0 : (p : 𝓞 E) ≠ 0` using `by first`. Consider the case `exact_mod_cast hp.ne_zero`. Consider the case `(intro h0`. Establish `h1` using `congrArg (fun t : 𝓞 E => (t : E)) h0`.

Simplify using `only [map_natCast, Nat.cast_eq_zero] at h1`. Conclude with `hp.ne_zero (by exact_mod_cast h1))`. Establish `hc : ((p : 𝓞 E) ^ a) ≠ 0` using `pow_ne_zero a hp0`. Establish `hI : Ideal.span {(p : 𝓞 E)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hp0`. Take `⟨e, q', q'', g⟩` from `glue_fin hP hO hE hN h' h'' hc ((Ideal.finite_factors hI).toFinset.image (fun v => v.asIdeal)) (by`. Introduce `P hPT`. Take `⟨v, -, rfl⟩` from `Finset.mem_image.mp hPT`. Conclude with `v.isMaximal)`.

Use `⟨e, q', q'', fun Q hQ hpQ => (g Q ?_).1⟩` and prove the remaining obligations. Use `Finset.mem_image.mpr ⟨⟨Q, hQ.isPrime, ne_bot_of_max hQ⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hpQ)`.
-/
theorem glue_of (hP : PowLoc) : Glue := by
  classical
  intro hO E _ _ _ hE N L' L'' hN h' h'' p hp a
  have hp0 : (p : 𝓞 E) ≠ 0 := by
    first
      | exact_mod_cast hp.ne_zero
      | (intro h0
         have h1 := congrArg (fun t : 𝓞 E => (t : E)) h0
         simp only [map_natCast, Nat.cast_eq_zero] at h1
         exact hp.ne_zero (by exact_mod_cast h1))
  have hc : ((p : 𝓞 E) ^ a) ≠ 0 := pow_ne_zero a hp0
  have hI : Ideal.span {(p : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp0
  obtain ⟨e, q', q'', g⟩ := glue_fin hP hO hE hN h' h'' hc
    ((Ideal.finite_factors hI).toFinset.image (fun v => v.asIdeal)) (by
      intro P hPT
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hPT
      exact v.isMaximal)
  refine ⟨e, q', q'', fun Q hQ hpQ => (g Q ?_).1⟩
  refine Finset.mem_image.mpr ⟨⟨Q, hQ.isPrime, ne_bot_of_max hQ⟩, ?_, rfl⟩
  rw [Set.Finite.mem_toFinset]
  exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hpQ)

end PI.SqPairLocal
