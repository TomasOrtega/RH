import Formalism.LocalToGlobal.CharacterGerms.RowTieValCut
import Formalism.LocalToGlobal.CharacterGerms.RowTieJet

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

section EqOn

variable {K : Type} [Field K] {σ : Type}

def EqOn (A : Set σ) (F G : MvPowerSeries σ K) : Prop :=
  ∀ μ : σ →₀ ℕ, (↑μ.support : Set σ) ⊆ A → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G

/- English proof (translation)
Introduce `_ _` and use `rfl`.
-/
theorem EqOn.refl (A : Set σ) (F : MvPowerSeries σ K) : EqOn A F F := fun _ _ => rfl

/- English proof (translation)
Introduce `μ hμ`. Rewrite using `[MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hs : p.1 + p.2 = μ` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`. Establish `h1 : (↑p.1.support : Set σ) ⊆ A` using `fun x hx => hμ (by`.

Establish `: p.1 ≤ μ` using `hs ▸ le_self_add`. Conclude with `Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))`. Establish `h2 : (↑p.2.support : Set σ) ⊆ A` using `fun x hx => hμ (by`. Establish `: p.2 ≤ μ` using `hs ▸ le_add_self`. Conclude with `Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))`.

Rewrite using `[h p.1 h1, h' p.2 h2]`.
-/
theorem EqOn.mul {A : Set σ} {F G F' G' : MvPowerSeries σ K} (h : EqOn A F G) (h' : EqOn A F' G') :
    EqOn A (F * F') (G * G') := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hs : p.1 + p.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have h1 : (↑p.1.support : Set σ) ⊆ A := fun x hx => hμ (by
    have : p.1 ≤ μ := hs ▸ le_self_add
    exact Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))
  have h2 : (↑p.2.support : Set σ) ⊆ A := fun x hx => hμ (by
    have : p.2 ≤ μ := hs ▸ le_add_self
    exact Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))
  rw [h p.1 h1, h' p.2 h2]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using EqOn.refl A (1 : MvPowerSeries σ K)`. Consider the case `succ k ih => rw [pow_succ, pow_succ]`. Conclude with `ih.mul h`.
-/
theorem EqOn.pow {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) (k : ℕ) : EqOn A (F ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using EqOn.refl A (1 : MvPowerSeries σ K)
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using EqOn.refl A (1 : MvPowerSeries σ K)`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem EqOn.prod {A : Set σ} {ι : Type} (s : Finset ι) {F G : ι → MvPowerSeries σ K}
    (h : ∀ i ∈ s, EqOn A (F i) (G i)) : EqOn A (∏ i ∈ s, F i) (∏ i ∈ s, G i) := by
  induction s using Finset.induction_on with
  | empty => simpa using EqOn.refl A (1 : MvPowerSeries σ K)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `μ hμ`. Use `show ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F ^ k) / (k.factorial : K) = ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (G ^ k) / (k.factorial : K)`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [h.pow k μ hμ]`.
-/
theorem EqOn.mvExp {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) : EqOn A (mvExp F) (mvExp G) := by
  intro μ hμ
  show ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F ^ k) / (k.factorial : K) =
    ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (G ^ k) / (k.factorial : K)
  exact Finset.sum_congr rfl fun k _ => by rw [h.pow k μ hμ]

/- English proof (translation)
Unfold `jetAt0`. Conclude with `Finset.sum_congr rfl fun μ hμ => by rw [h μ (hP μ hμ)]`.
-/
theorem EqOn.jet {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) (P : MvPolynomial σ K)
    (hP : ∀ μ ∈ P.support, (↑μ.support : Set σ) ⊆ A) : jetAt0 P F = jetAt0 P G := by
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [h μ (hP μ hμ)]

/- English proof (translation)
Introduce `ν hν`. Distinguish the cases in `hr : ν ∈ Set.range (Finsupp.mapDomain e)`. Take `⟨μ, rfl⟩` from `hr`. Rewrite using `[← Finsupp.embDomain_eq_mapDomain, MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_embDomain_rename]`. Use `h μ fun x hx => hν ?_` and prove the remaining obligations.

Rewrite using `[← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain]`. Conclude with `Finset.mem_coe.2 (Finset.mem_map_of_mem e hx)`. Rewrite using `[MvPowerSeries.coeff_rename_eq_zero _ _ hr, MvPowerSeries.coeff_rename_eq_zero _ _ hr]`.
-/
theorem EqOn.rename {τ : Type} (e : σ ↪ τ) {A : Set τ} {F G : MvPowerSeries σ K}
    (h : ∀ μ : σ →₀ ℕ, (∀ x ∈ μ.support, e x ∈ A) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G) :
    EqOn A (MvPowerSeries.rename e F) (MvPowerSeries.rename e G) := by
  intro ν hν
  by_cases hr : ν ∈ Set.range (Finsupp.mapDomain e)
  · obtain ⟨μ, rfl⟩ := hr
    rw [← Finsupp.embDomain_eq_mapDomain, MvPowerSeries.coeff_embDomain_rename,
      MvPowerSeries.coeff_embDomain_rename]
    refine h μ fun x hx => hν ?_
    rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain]
    exact Finset.mem_coe.2 (Finset.mem_map_of_mem e hx)
  · rw [MvPowerSeries.coeff_rename_eq_zero _ _ hr, MvPowerSeries.coeff_rename_eq_zero _ _ hr]

end EqOn

/- English proof (translation)
Introduce `C _ V d _ I _ κ _ X H n Po kind hk gr`. Rewrite using `[rtj_valOf]`. Use `set A : Set (Fin n × WV I) := {x | ∃ μ ∈ Po.support, μ x ≠ 0} with hA`. Use `EqOn.jet (A := A) ?_ Po fun μ hμ x hx => ⟨μ, hμ, Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hx)⟩` and prove the remaining obligations. Use `EqOn.prod _ fun ρ _ => (EqOn.refl A _).mul (EqOn.mvExp ?_)` and prove the remaining obligations.

Rewrite using `[rtj_rowCopy_eq, rtj_rowCopy_eq]`. Use `EqOn.rename (rtjR ρ) fun μ hμ => ?_` and prove the remaining obligations. Consider the cases of `hkd : kind ρ with`. Consider the case `none`. Take `⟨g, hg⟩` from `hk.2 ρ hkd`.

Establish `h1 : ∀ w ∈ μ.support, w.1 = g` using `fun w hw => by`. Take `⟨μ', hμ', hne⟩` from `hμ w hw`. Conclude with `hg μ' hμ' w hne`. Establish `h2 : (∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1)` using `by fin_cases g`. Conclude with `Or.inl h1`.

Conclude with `Or.inr h1`. Rewrite using `[H.axes μ h2]`. Simplify using `[rtjH]`. Consider the case `some q`. Take `⟨g, a, a'⟩` from `q`.

Establish `h1 : ∀ w ∈ μ.support, X.OnLf g a a' w` using `fun w hw => by`. Take `⟨μ', hμ', hne⟩` from `hμ w hw`. Conclude with `(hk.1 ρ g a a' hkd).2.2 μ' hμ' w hne`. Use `show MvPowerSeries.coeff μ X.hRow = (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0)`. Rewrite using `[if_pos h1]`.
-/
theorem leaf_holds : LeafSt := by
  intro C _ V d _ I _ κ _ X H n Po kind hk gr
  rw [rtj_valOf]
  set A : Set (Fin n × WV I) := {x | ∃ μ ∈ Po.support, μ x ≠ 0} with hA
  refine EqOn.jet (A := A) ?_ Po fun μ hμ x hx => ⟨μ, hμ, Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hx)⟩
  refine EqOn.prod _ fun ρ _ => (EqOn.refl A _).mul (EqOn.mvExp ?_)
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq]
  refine EqOn.rename (rtjR ρ) fun μ hμ => ?_
  cases hkd : kind ρ with
  | none =>
    obtain ⟨g, hg⟩ := hk.2 ρ hkd
    have h1 : ∀ w ∈ μ.support, w.1 = g := fun w hw => by
      obtain ⟨μ', hμ', hne⟩ := hμ w hw
      exact hg μ' hμ' w hne
    have h2 : (∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1) := by
      fin_cases g
      · exact Or.inl h1
      · exact Or.inr h1
    rw [H.axes μ h2]
    simp [rtjH]
  | some q =>
    obtain ⟨g, a, a'⟩ := q
    have h1 : ∀ w ∈ μ.support, X.OnLf g a a' w := fun w hw => by
      obtain ⟨μ', hμ', hne⟩ := hμ w hw
      exact (hk.1 ρ g a a' hkd).2.2 μ' hμ' w hne
    show MvPowerSeries.coeff μ X.hRow =
      (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0)
    rw [if_pos h1]

end Formalism.L2.FormalSeriesBounds
