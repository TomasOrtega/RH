import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.IntegralityIffAwayAtD

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

section Pd

variable {σ : Type*} {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_pderiv, mul_comm]`. Both sides reduce to the same expression.
-/
theorem pd_eq (inst : DecidableEq σ) (k : σ) (F : MvPowerSeries σ ℂ_[p]) :
    @pd σ inst ℂ_[p] _ k F = MvPowerSeries.pderiv ℂ_[p] k F := by
  ext n
  rw [MvPowerSeries.coeff_pderiv, mul_comm]
  rfl

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [MvPowerSeries.coeff_pderiv, Finsupp.add_apply]`. Rewrite using `[add_right_comm n (Finsupp.single j 1) (Finsupp.single i 1)]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Both sides reduce to the same expression. Simplify using `only [Finsupp.single_apply, if_neg h, if_neg (Ne.symm h), add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pderiv_comm (i j : σ) (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.pderiv ℂ_[p] i (MvPowerSeries.pderiv ℂ_[p] j F) =
      MvPowerSeries.pderiv ℂ_[p] j (MvPowerSeries.pderiv ℂ_[p] i F) := by
  ext n
  simp only [MvPowerSeries.coeff_pderiv, Finsupp.add_apply]
  rw [add_right_comm n (Finsupp.single j 1) (Finsupp.single i 1)]
  by_cases h : i = j
  · subst h
    rfl
  · simp only [Finsupp.single_apply, if_neg h, if_neg (Ne.symm h), add_zero]
    ring

/- English proof (translation)
Rewrite using `[Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero, smul_eq_mul]`.
-/
theorem pderiv_C_mul (k : σ) (c : ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.pderiv ℂ_[p] k (algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) c * F) =
      algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) c * MvPowerSeries.pderiv ℂ_[p] k F := by
  rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero, smul_eq_mul]

end Pd

section Der

variable {D : D7} {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

local notation "Ser" => MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]

/- English proof (translation)
Simplify using `only [der, pd_eq]`.
-/
theorem der_eq (y : Matrix (Fin N') (Fin N) D.host.E) (F : Ser) :
    der D lam y F = ∑ k : D.what₂.Tau × Fin N' × Fin N,
      algebraMap ℂ_[p] Ser (lamC lam (embT D k.1 (y k.2.1 k.2.2))) * MvPowerSeries.pderiv ℂ_[p] k F := by
  simp only [der, pd_eq]

/- English proof (translation)
Simplify using `only [der_eq, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem der_add (y : Matrix (Fin N') (Fin N) D.host.E) (F G : Ser) :
    der D lam y (F + G) = der D lam y F + der D lam y G := by
  simp only [der_eq, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [der_eq, map_zero, mul_zero, Finset.sum_const_zero]`.
-/
theorem der_zero (y : Matrix (Fin N') (Fin N) D.host.E) : der D lam y (0 : Ser) = 0 := by
  simp only [der_eq, map_zero, mul_zero, Finset.sum_const_zero]

/- English proof (translation)
Rewrite using `[der_eq, der_eq, der_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem der_mul (y : Matrix (Fin N') (Fin N) D.host.E) (F G : Ser) :
    der D lam y (F * G) = F * der D lam y G + G * der D lam y F := by
  rw [der_eq, der_eq, der_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

/- English proof (translation)
Simplify using `only [der_eq, Derivation.map_algebraMap, mul_zero, Finset.sum_const_zero]`.
-/
theorem der_C (y : Matrix (Fin N') (Fin N) D.host.E) (c : ℂ_[p]) :
    der D lam y (algebraMap ℂ_[p] Ser c) = 0 := by
  simp only [der_eq, Derivation.map_algebraMap, mul_zero, Finset.sum_const_zero]

/- English proof (translation)
Simplify using `only [der_eq, map_sum, pderiv_C_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_comm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem der_comm (a b : Matrix (Fin N') (Fin N) D.host.E) (F : Ser) :
    der D lam a (der D lam b F) = der D lam b (der D lam a F) := by
  simp only [der_eq, map_sum, pderiv_C_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [pderiv_comm]
  ring

def Dl (l : List (Matrix (Fin N') (Fin N) D.host.E)) (F : Ser) : Ser :=
  l.foldr (fun y' G => der D lam y' G) F

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Dl_nil (F : Ser) : Dl lam [] F = F := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Dl_cons (a : Matrix (Fin N') (Fin N) D.host.E) (l : List (Matrix (Fin N') (Fin N) D.host.E)) (F : Ser) :
    Dl lam (a :: l) F = der D lam a (Dl lam l F) := rfl

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons a l ih => rw [Dl_cons, Dl_cons, Dl_cons, ih, der_add]`.
-/
theorem Dl_add (l : List (Matrix (Fin N') (Fin N) D.host.E)) (F G : Ser) :
    Dl lam l (F + G) = Dl lam l F + Dl lam l G := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [Dl_cons, Dl_cons, Dl_cons, ih, der_add]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons a l ih => rw [Dl_cons, ih, der_zero]`.
-/
theorem Dl_zero (l : List (Matrix (Fin N') (Fin N) D.host.E)) : Dl lam l (0 : Ser) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [Dl_cons, ih, der_zero]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons b l ih => rw [Dl_cons, Dl_cons, der_comm, ih]`.
-/
theorem der_Dl (a : Matrix (Fin N') (Fin N) D.host.E) (l : List (Matrix (Fin N') (Fin N) D.host.E)) (F : Ser) :
    der D lam a (Dl lam l F) = Dl lam l (der D lam a F) := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [Dl_cons, Dl_cons, der_comm, ih]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons b l ih => rw [List.cons_append, Dl_cons, ih, Dl_cons]`.
-/
theorem Dl_append_single (l : List (Matrix (Fin N') (Fin N) D.host.E)) (a : Matrix (Fin N') (Fin N) D.host.E)
    (F : Ser) : Dl lam (l ++ [a]) F = Dl lam l (der D lam a F) := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.cons_append, Dl_cons, ih, Dl_cons]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h l hl`. Establish `h1` using `h l.length l.get (fun i => hl _ (by simp))`. Rewrite `h1` using `[List.ofFn_get]`. Conclude with `h1`.

Introduce `h n y hy`. Use `h (List.ofFn y) (fun z hz => ?_)` and prove the remaining obligations. Rewrite `hz` using `[List.mem_ofFn]`. Take `⟨i, rfl⟩` from `hz`. Conclude with `hy i`.
-/
theorem jetsInt_iff (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (F : Ser) :
    JetsInt D lam Y F ↔ ∀ l : List (Matrix (Fin N') (Fin N) D.host.E), (∀ y ∈ l, y ∈ Y) →
      IsIntP (MvPowerSeries.constantCoeff (Dl lam l F)) := by
  constructor
  · intro h l hl
    have h1 := h l.length l.get (fun i => hl _ (by simp))
    rw [List.ofFn_get] at h1
    exact h1
  · intro h n y hy
    refine h (List.ofFn y) (fun z hz => ?_)
    rw [List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact hy i

variable {lam}

/- English proof (translation)
Rewrite `hF`, the goal using `[jetsInt_iff]`. Introduce `l hl`. Rewrite using `[← Dl_append_single]`. Use `hF _ (fun y hy => ?_)` and prove the remaining obligations. Break down `List.mem_append.1 hy with h | h` into its components or cases.

Conclude with `hl y h`. Rewrite using `[List.mem_singleton.1 h]`. Conclude with `ha`.
-/
theorem jetsInt_der {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)} {F : Ser}
    (hF : JetsInt D lam Y F) {a : Matrix (Fin N') (Fin N) D.host.E} (ha : a ∈ Y) :
    JetsInt D lam Y (der D lam a F) := by
  rw [jetsInt_iff] at hF ⊢
  intro l hl
  rw [← Dl_append_single]
  refine hF _ (fun y hy => ?_)
  rcases List.mem_append.1 hy with h | h
  · exact hl y h
  · rw [List.mem_singleton.1 h]
    exact ha

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)`.
-/
theorem isPadicIntegral_add {x y : ℂ_[p]} (hx : IsIntP x) (hy : IsIntP y) : IsIntP (x + y) :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

/- English proof (translation)
Rewrite `hF`, `hG`, the goal using `[jetsInt_iff]`. Introduce `l hl`. Rewrite using `[Dl_add, map_add]`. Conclude with `isPadicIntegral_add (hF l hl) (hG l hl)`.
-/
theorem jetsInt_add {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)} {F G : Ser}
    (hF : JetsInt D lam Y F) (hG : JetsInt D lam Y G) : JetsInt D lam Y (F + G) := by
  rw [jetsInt_iff] at hF hG ⊢
  intro l hl
  rw [Dl_add, map_add]
  exact isPadicIntegral_add (hF l hl) (hG l hl)

/- English proof (translation)
Rewrite using `[jetsInt_iff]`. Introduce `l hl`. Proceed by induction on `l generalizing F G with`. Consider the case `nil`. Establish `hF0` using `(jetsInt_iff _ _ _).1 hF [] (by simp)`.

Establish `hG0` using `(jetsInt_iff _ _ _).1 hG [] (by simp)`. Rewrite `hF0`, `hG0`, the goal using `[Dl_nil]`. Use `show ‖MvPowerSeries.constantCoeff (F * G)‖ ≤ 1`. Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_one₀ hF0 (norm_nonneg _) hG0`.

Consider the case `cons a l ih`. Establish `ha : a ∈ Y` using `hl a (by simp)`. Establish `hl' : ∀ y ∈ l, y ∈ Y` using `fun y hy => hl y (by simp [hy])`. Rewrite using `[Dl_cons, der_Dl, der_mul, Dl_add, map_add]`. Conclude with `isPadicIntegral_add (ih hF (jetsInt_der hG ha) hl') (ih hG (jetsInt_der hF ha) hl')`.
-/
theorem jetsInt_mul {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)} {F G : Ser}
    (hF : JetsInt D lam Y F) (hG : JetsInt D lam Y G) : JetsInt D lam Y (F * G) := by
  rw [jetsInt_iff]
  intro l hl
  induction l generalizing F G with
  | nil =>
    have hF0 := (jetsInt_iff _ _ _).1 hF [] (by simp)
    have hG0 := (jetsInt_iff _ _ _).1 hG [] (by simp)
    rw [Dl_nil] at hF0 hG0 ⊢
    show ‖MvPowerSeries.constantCoeff (F * G)‖ ≤ 1
    rw [map_mul, norm_mul]
    exact mul_le_one₀ hF0 (norm_nonneg _) hG0
  | cons a l ih =>
    have ha : a ∈ Y := hl a (by simp)
    have hl' : ∀ y ∈ l, y ∈ Y := fun y hy => hl y (by simp [hy])
    rw [Dl_cons, der_Dl, der_mul, Dl_add, map_add]
    exact isPadicIntegral_add (ih hF (jetsInt_der hG ha) hl') (ih hG (jetsInt_der hF ha) hl')

/- English proof (translation)
Rewrite using `[jetsInt_iff]`. Introduce `l hl`. Consider the cases of `l with`. Consider the case `nil`. Rewrite using `[Dl_nil]`.

Establish `h0 : MvPowerSeries.constantCoeff (algebraMap ℂ_[p] Ser c) = c` using `by first`. Consider the case `rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.constantCoeff_C]`. Consider the case `simp [MvPowerSeries.algebraMap_apply]`. Rewrite using `[h0]`. Conclude with `hc`.

Consider the case `cons a l`. Rewrite using `[Dl_cons, der_Dl, der_C, Dl_zero, map_zero]`. Use `show ‖(0 : ℂ_[p])‖ ≤ 1`. Simplify using the standard rewrite rules.
-/
theorem jetsInt_C {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)} {c : ℂ_[p]} (hc : IsIntP c) :
    JetsInt D lam Y (algebraMap ℂ_[p] Ser c) := by
  rw [jetsInt_iff]
  intro l hl
  cases l with
  | nil =>
    rw [Dl_nil]
    have h0 : MvPowerSeries.constantCoeff (algebraMap ℂ_[p] Ser c) = c := by
      first
        | rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.constantCoeff_C]
        | simp [MvPowerSeries.algebraMap_apply]
    rw [h0]
    exact hc
  | cons a l =>
    rw [Dl_cons, der_Dl, der_C, Dl_zero, map_zero]
    show ‖(0 : ℂ_[p])‖ ≤ 1
    simp

/- English proof (translation)
Rewrite using `[jetsInt_iff]`. Introduce `l hl`. Rewrite using `[Dl_zero, map_zero]`. Use `show ‖(0 : ℂ_[p])‖ ≤ 1`. Simplify using the standard rewrite rules.
-/
theorem jetsInt_zero {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)} :
    JetsInt D lam Y (0 : Ser) := by
  rw [jetsInt_iff]
  intro l hl
  rw [Dl_zero, map_zero]
  show ‖(0 : ℂ_[p])‖ ≤ 1
  simp

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Rewrite using `[Finset.sum_empty]`. Conclude with `jetsInt_zero`.

Introduce `i s hi ih h`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `jetsInt_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem jetsInt_sum {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)} {ι : Type*} (s : Finset ι)
    (F : ι → Ser) (h : ∀ i ∈ s, JetsInt D lam Y (F i)) : JetsInt D lam Y (∑ i ∈ s, F i) := by
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact jetsInt_zero
  · intro i s hi ih h
    rw [Finset.sum_insert hi]
    exact jetsInt_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Der

/- English proof (translation)
Take `⟨m, r, t, L₁, L₁', hr, ht, hA, rfl⟩` from `hF`. Use `jetsInt_sum _ _ fun k _ => jetsInt_mul (jetsInt_C (hr k)) ?_` and prove the remaining obligations. Conclude with `h1 (t k) (L₁ k) (L₁' k) (ht k) (hA k).1 (hA k).2.1 (hA k).2.2`.
-/
theorem jetsInt_of_comb {D : D7} (T : Tor D) (e : FamE D) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h1 : ∀ (t : VC D N N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TorsPrime D p (La D T L L') t →
      admitted D N N' L₁ L₁' → EqAt D p L L₁ → EqAt D p L' L₁' →
      JetsInt D lam (YYl D L L') (pSer D lam (U D T t (e N N' L₁ L₁'))))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (hF : IsComb D T e lam L L' F) :
    JetsInt D lam (YYl D L L') F := by
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hA, rfl⟩ := hF
  refine jetsInt_sum _ _ fun k _ => jetsInt_mul (jetsInt_C (hr k)) ?_
  exact h1 (t k) (L₁ k) (L₁' k) (ht k) (hA k).1 (hA k).2.1 (hA k).2.2

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
