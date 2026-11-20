import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

/- English proof (translation)
Establish `key : ∀ {A B : Ideal R}, (∀ x ∈ A, ∃ s, s ∉ W ∧ s * x ∈ B) → Submodule.localized W.primeCompl (M` using `R) A ≤ Submodule.localized W.primeCompl (M := R) B := by`. Introduce `A B h y hy`. Take `⟨m, hm, s, rfl⟩` from `hy`. Take `⟨t, ht, htm⟩` from `h m hm`. Use `⟨t * m, htm, ⟨t, ht⟩ * s, ?_⟩` and prove the remaining obligations.

Conclude with `IsLocalizedModule.mk'_cancel_left _ _ _ _`. Establish `heq : Submodule.localized W.primeCompl (M` using `R) J₁ = Submodule.localized W.primeCompl (M := R) J₂ := le_antisymm (key h₁) (key h₂)`. Establish `e₁` using `(localizedQuotientEquiv W.primeCompl (M := R) J₁).length_eq`. Establish `e₂` using `(localizedQuotientEquiv W.primeCompl (M := R) J₂).length_eq`. Establish `e₃` using `(Submodule.quotEquivOfEq _ _ heq).length_eq`.

Conclude with `e₁.symm.trans (e₃.trans e₂)`.
-/
theorem length_localizedModule_quot_eq {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] {J₁ J₂ : Ideal R}
    (h₁ : ∀ x ∈ J₁, ∃ s, s ∉ W ∧ s * x ∈ J₂) (h₂ : ∀ x ∈ J₂, ∃ s, s ∉ W ∧ s * x ∈ J₁) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₁)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₂)) := by
  have key : ∀ {A B : Ideal R}, (∀ x ∈ A, ∃ s, s ∉ W ∧ s * x ∈ B) →
      Submodule.localized W.primeCompl (M := R) A ≤ Submodule.localized W.primeCompl (M := R) B := by
    intro A B h y hy
    obtain ⟨m, hm, s, rfl⟩ := hy
    obtain ⟨t, ht, htm⟩ := h m hm
    refine ⟨t * m, htm, ⟨t, ht⟩ * s, ?_⟩
    exact IsLocalizedModule.mk'_cancel_left _ _ _ _
  have heq : Submodule.localized W.primeCompl (M := R) J₁ = Submodule.localized W.primeCompl (M := R) J₂ :=
    le_antisymm (key h₁) (key h₂)
  have e₁ := (localizedQuotientEquiv W.primeCompl (M := R) J₁).length_eq
  have e₂ := (localizedQuotientEquiv W.primeCompl (M := R) J₂).length_eq
  have e₃ := (Submodule.quotEquivOfEq _ _ heq).length_eq
  exact e₁.symm.trans (e₃.trans e₂)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `W hW hP hR`. Take `⟨u, v, hu, hv, hm⟩` from `h W hW hP hR`. Use `⟨v, u, hv, hu, ?_⟩` and prove the remaining obligations. Use `P.neg_mem hm` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis.
-/
theorem IsUnitSec.symm {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) : IsUnitSec P g f := by
  intro W hW hP hR
  obtain ⟨u, v, hu, hv, hm⟩ := h W hW hP hR
  refine ⟨v, u, hv, hu, ?_⟩
  have := P.neg_mem hm
  rwa [neg_sub] at this

/- English proof (translation)
Introduce and unpack `W ⟨hmin, hrel⟩`. Establish `hWp : W.IsPrime` using `hmin.1.1`. Establish `hP : P ≤ W` using `le_sup_left.trans hmin.1.2`. Establish `hf : f ∈ W` using `hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))`. Take `⟨u, v, hu, hv, hm⟩` from `h W hWp hP hrel`.

Establish `hvg : v * g ∈ W`. Establish `e : v * g = u * f - (u * f - v * g)` using `by ring`. Rewrite using `[e]`. Conclude with `W.sub_mem (W.mul_mem_left u hf) (hP hm)`. Establish `hg : g ∈ W` using `(hWp.mem_or_mem hvg).resolve_left hv`.

Use `⟨⟨⟨hWp, sup_le hP ((Ideal.span_singleton_le_iff_mem _).mpr hg)⟩, ?_⟩, hrel⟩` and prove the remaining obligations. Introduce and unpack `W' ⟨hW'p, hW'le⟩ hW'W`. Establish `hP' : P ≤ W'` using `le_sup_left.trans hW'le`. Establish `hg' : g ∈ W'` using `hW'le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))`. Establish `huf : u * f ∈ W'`.

Establish `e : u * f = (u * f - v * g) + v * g` using `by ring`. Rewrite using `[e]`. Conclude with `W'.add_mem (hP' hm) (W'.mul_mem_left v hg')`. Establish `hf' : f ∈ W'` using `(hW'p.mem_or_mem huf).resolve_left fun hu' => hu (hW'W hu')`. Conclude with `hmin.2 ⟨hW'p, sup_le hP' ((Ideal.span_singleton_le_iff_mem _).mpr hf')⟩ hW'W`.
-/
theorem divSupp_subset_of_isUnitSec {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) :
    divSupp P f ⊆ divSupp P g := by
  rintro W ⟨hmin, hrel⟩
  have hWp : W.IsPrime := hmin.1.1
  have hP : P ≤ W := le_sup_left.trans hmin.1.2
  have hf : f ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨u, v, hu, hv, hm⟩ := h W hWp hP hrel
  have hvg : v * g ∈ W := by
    have e : v * g = u * f - (u * f - v * g) := by ring
    rw [e]
    exact W.sub_mem (W.mul_mem_left u hf) (hP hm)
  have hg : g ∈ W := (hWp.mem_or_mem hvg).resolve_left hv
  refine ⟨⟨⟨hWp, sup_le hP ((Ideal.span_singleton_le_iff_mem _).mpr hg)⟩, ?_⟩, hrel⟩
  rintro W' ⟨hW'p, hW'le⟩ hW'W
  have hP' : P ≤ W' := le_sup_left.trans hW'le
  have hg' : g ∈ W' := hW'le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have huf : u * f ∈ W' := by
    have e : u * f = (u * f - v * g) + v * g := by ring
    rw [e]
    exact W'.add_mem (hP' hm) (W'.mul_mem_left v hg')
  have hf' : f ∈ W' := (hW'p.mem_or_mem huf).resolve_left fun hu' => hu (hW'W hu')
  exact hmin.2 ⟨hW'p, sup_le hP' ((Ideal.span_singleton_le_iff_mem _).mpr hf')⟩ hW'W

/- English proof (translation)
Take `⟨p, hp, y, hy, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Establish `e : u * (p + a * f) = (u * p + a * (u * f - v * g)) + (a * v) * g` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left (P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left a hm))) (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))`.
-/
theorem mul_mem_sup_span_of_sub_mem {R : Type*} [CommRing R] {P : Ideal R} {f g u v x : R}
    (hm : u * f - v * g ∈ P) (hx : x ∈ P ⊔ Ideal.span {f}) : u * x ∈ P ⊔ Ideal.span {g} := by
  obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have e : u * (p + a * f) = (u * p + a * (u * f - v * g)) + (a * v) * g := by ring
  rw [e]
  exact Ideal.add_mem _
    (Ideal.mem_sup_left (P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left a hm)))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))

/- English proof (translation)
Establish `hm' : v * g - u * f ∈ P`. Use `P.neg_mem hm` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Use `haveI := hW`. Unfold `multAt`.

Rewrite using `[dif_pos hW, dif_pos hW, length_localizedModule_quot_eq W (fun x hx => ⟨u, hu, mul_mem_sup_span_of_sub_mem hm hx⟩) (fun x hx => ⟨v, hv, mul_mem_sup_span_of_sub_mem hm' hx⟩)]`.
-/
theorem multAt_sup_span_eq_of_sub_mem {P W : Ideal (MRing ι)} (hW : W.IsPrime) {f g u v : MRing ι}
    (hu : u ∉ W) (hv : v ∉ W) (hm : u * f - v * g ∈ P) :
    multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  have hm' : v * g - u * f ∈ P := by
    have := P.neg_mem hm
    rwa [neg_sub] at this
  haveI := hW
  unfold multAt
  rw [dif_pos hW, dif_pos hW,
    length_localizedModule_quot_eq W
      (fun x hx => ⟨u, hu, mul_mem_sup_span_of_sub_mem hm hx⟩)
      (fun x hx => ⟨v, hv, mul_mem_sup_span_of_sub_mem hm' hx⟩)]

/- English proof (translation)
Introduce `K _ ι _ P f g h`. Establish `hsupp : divSupp P f = divSupp P g` using `Set.Subset.antisymm (divSupp_subset_of_isUnitSec h) (divSupp_subset_of_isUnitSec h.symm)`. Establish `hmult : ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W`. Introduce and unpack `W ⟨hmin, hrel⟩`. Establish `hWp : W.IsPrime` using `hmin.1.1`.

Take `⟨u, v, hu, hv, hm⟩` from `h W hWp (le_sup_left.trans hmin.1.2) hrel`. Conclude with `multAt_sup_span_eq_of_sub_mem hWp hu hv hm`. Use `⟨hsupp, hmult, fun n L => ?_⟩` and prove the remaining obligations. Unfold `vertR`. Rewrite using `[← hsupp]`.

Use `finsum_mem_congr rfl fun W hW => ?_` and prove the remaining obligations. Rewrite using `[hmult W hW]`.
-/
theorem cycles_eq_of_isUnitSec :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι),
      IsUnitSec P f g → divSupp P f = divSupp P g ∧
        (∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W) ∧
        ∀ (n : ℕ) (L : Fin n → HermLine ι), vertR P L f = vertR P L g := by
  intro K _ ι _ P f g h
  have hsupp : divSupp P f = divSupp P g :=
    Set.Subset.antisymm (divSupp_subset_of_isUnitSec h) (divSupp_subset_of_isUnitSec h.symm)
  have hmult : ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
    rintro W ⟨hmin, hrel⟩
    have hWp : W.IsPrime := hmin.1.1
    obtain ⟨u, v, hu, hv, hm⟩ := h W hWp (le_sup_left.trans hmin.1.2) hrel
    exact multAt_sup_span_eq_of_sub_mem hWp hu hv hm
  refine ⟨hsupp, hmult, fun n L => ?_⟩
  unfold vertR
  rw [← hsupp]
  refine finsum_mem_congr rfl fun W hW => ?_
  rw [hmult W hW]

end GlobalTheory.CompanionTheory.Ar.Flat
