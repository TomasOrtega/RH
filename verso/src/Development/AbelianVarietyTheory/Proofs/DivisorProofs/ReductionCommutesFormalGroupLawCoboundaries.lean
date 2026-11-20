import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralReducingToMvPowerSeriesSubst
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz.RedCob

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ τ : Type} {d : ℕ}

def Pt (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ τ : Type}
    (u : σ → MvPowerSeries τ (Fr p k)) (u' : σ → MvPowerSeries τ k) : Prop :=
  (∀ i, constantCoeff (u i) = 0) ∧ ∀ i, Red p (u i) (u' i)

variable [PerfectRing k p]

/- English proof (translation)
The claim follows from `(GlobalTheory.Katz.red_subst p k σ τ u u' h.1 h.2).1 f f' hf`.
-/
theorem red_subst [Finite σ] {u : σ → MvPowerSeries τ (Fr p k)} {u' : σ → MvPowerSeries τ k}
    (h : Pt p u u') {f : MvPowerSeries σ (Fr p k)} {f' : MvPowerSeries σ k} (hf : Red p f f') :
    Red p (subst u f) (subst u' f') :=
  (GlobalTheory.Katz.red_subst p k σ τ u u' h.1 h.2).1 f f' hf

end GlobalTheory.Katz.RedCob

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.Katz.Red`. Introduce `α`. Conclude with `⟨WittVector.teichmuller p (coeff α f), _root_.GlobalTheory.Katz.coeff_lift p f α, by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩`.
-/
private theorem red_lift_self [CharP k p] {σ : Type} (f : MvPowerSeries σ k) :
    _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.lift p f) f := by
  unfold _root_.GlobalTheory.Katz.Red
  intro α
  exact ⟨WittVector.teichmuller p (coeff α f), _root_.GlobalTheory.Katz.coeff_lift p f α,
    by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
omit [CharP k p] [PerfectRing k p] in
/- English proof (translation)
Establish `h : ∀ s, constantCoeff (Sum.elim a b s) = 0`. Introduce and unpack `(i | i)`. Conclude with `ha₀ i`. Conclude with `hb₀ i`. Conclude with `constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h hf`.
-/
private theorem constantCoeff_at2_eq_zero {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) R} {a b : Fin d → MvPowerSeries τ R}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (hf : constantCoeff f = 0) : constantCoeff (_root_.GlobalTheory.Katz.at2 f a b) = 0 := by
  have h : ∀ s, constantCoeff (Sum.elim a b s) = 0 := by
    rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h hf

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.Katz.at2`. Use `(_root_.GlobalTheory.Katz.red_subst p k (Fin d ⊕ Fin d) τ (Sum.elim a b) (Sum.elim a' b') ?_ ?_).1 f f' hf` and prove the remaining obligations. Introduce and unpack `(i | i)`. Conclude with `ha₀ i`. Conclude with `hb₀ i`.

Introduce and unpack `(i | i)`. Conclude with `ha i`. Conclude with `hb i`.
-/
private theorem red_at2_of_red {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    {f' : MvPowerSeries (Fin d ⊕ Fin d) k}
    {a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k)} {a' b' : Fin d → MvPowerSeries τ k}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (ha : ∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i))
    (hb : ∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i))
    (hf : _root_.GlobalTheory.Katz.Red p f f') :
    _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.at2 f a b)
      (_root_.GlobalTheory.Katz.at2 f' a' b') := by
  unfold _root_.GlobalTheory.Katz.at2
  refine (_root_.GlobalTheory.Katz.red_subst p k (Fin d ⊕ Fin d) τ (Sum.elim a b)
    (Sum.elim a' b') ?_ ?_).1 f f' hf
  · rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  · rintro (i | i)
    · exact ha i
    · exact hb i

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.Katz.Red`. Introduce `α`. Use `⟨if α = Finsupp.single s 1 then 1 else 0, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [coeff_X]; split_ifs <;> simp`. Apply the tactic sequence `rw [coeff_X]; split_ifs <;> simp`.
-/
private theorem red_X' {σ : Type} (s : σ) :
    _root_.GlobalTheory.Katz.Red p (X s : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k))
      (X s) := by
  classical
  unfold _root_.GlobalTheory.Katz.Red
  intro α
  refine ⟨if α = Finsupp.single s 1 then 1 else 0, ?_, ?_⟩
  · rw [coeff_X]; split_ifs <;> simp
  · rw [coeff_X]; split_ifs <;> simp

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.Katz.Red at *`. Introduce `α`. Take `⟨v, hv, hv'⟩` from `hf α`. Take `⟨w, hw, hw'⟩` from `hg α`. Conclude with `⟨v - w, by rw [map_sub, map_sub, hv, hw], by rw [map_sub, map_sub, hv', hw']⟩`.
-/
private theorem red_sub_divisor {σ : Type} {f g : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k)}
    {f' g' : MvPowerSeries σ k} (hf : _root_.GlobalTheory.Katz.Red p f f')
    (hg : _root_.GlobalTheory.Katz.Red p g g') :
    _root_.GlobalTheory.Katz.Red p (f - g) (f' - g') := by
  unfold _root_.GlobalTheory.Katz.Red at *
  intro α
  obtain ⟨v, hv, hv'⟩ := hf α
  obtain ⟨w, hw, hw'⟩ := hg α
  exact ⟨v - w, by rw [map_sub, map_sub, hv, hw], by rw [map_sub, map_sub, hv', hw']⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.Katz.Red at *`. Introduce `α`. Take `⟨v, hv, hv'⟩` from `hf α`. Take `⟨w, hw, hw'⟩` from `hg α`. Conclude with `⟨v + w, by rw [map_add, map_add, hv, hw], by rw [map_add, map_add, hv', hw']⟩`.
-/
private theorem red_add_divisor {σ : Type} {f g : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k)}
    {f' g' : MvPowerSeries σ k} (hf : _root_.GlobalTheory.Katz.Red p f f')
    (hg : _root_.GlobalTheory.Katz.Red p g g') :
    _root_.GlobalTheory.Katz.Red p (f + g) (f' + g') := by
  unfold _root_.GlobalTheory.Katz.Red at *
  intro α
  obtain ⟨v, hv, hv'⟩ := hf α
  obtain ⟨w, hw, hw'⟩ := hg α
  exact ⟨v + w, by rw [map_add, map_add, hv, hw], by rw [map_add, map_add, hv', hw']⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.Katz.at2`. Use `(_root_.GlobalTheory.Katz.red_subst p k (Fin d ⊕ Fin d) τ (Sum.elim a b) (Sum.elim a' b') ?_ ?_).2 c f hf` and prove the remaining obligations. Introduce and unpack `(i | i)`. Conclude with `ha₀ i`. Conclude with `hb₀ i`.

Introduce and unpack `(i | i)`. Conclude with `ha i`. Conclude with `hb i`.
-/
private theorem at2_mem_intBy_of_red {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    {a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k)} {a' b' : Fin d → MvPowerSeries τ k}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (ha : ∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i))
    (hb : ∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i)) (c : WittVector p k)
    (hf : f ∈ _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) c) :
    _root_.GlobalTheory.Katz.at2 f a b ∈ _root_.GlobalTheory.Katz.intBy p k τ c := by
  unfold _root_.GlobalTheory.Katz.at2
  refine (_root_.GlobalTheory.Katz.red_subst p k (Fin d ⊕ Fin d) τ (Sum.elim a b)
    (Sum.elim a' b') ?_ ?_).2 c f hf
  · rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  · rintro (i | i)
    · exact ha i
    · exact hb i

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in

/- English proof (translation)
Introduce `p _ k _ _ _ d μ hμ`. Establish `hL₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.lift p (μ i)) = 0` using `fun i => _root_.GlobalTheory.Katz.constantCoeff_lift p (hμ i)`. Establish `hL : ∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.lift p (μ i)) (μ i)` using `fun i => red_lift_self (μ i)`. Establish `hop : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k)) (a' b' : Fin d → MvPowerSeries τ k), (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) → (∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i)) → (∀ i, _root_.GlobalTheory.Katz.Red p (b …`. Introduce `τ a b a' b' ha₀ hb₀ ha hb`.

Conclude with `⟨fun i => constantCoeff_at2_eq_zero ha₀ hb₀ (hL₀ i), fun i => red_at2_of_red ha₀ hb₀ ha hb (hL i)⟩`. Establish `hx₁₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x1 i : MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0` using `fun i => constantCoeff_X _`. Establish `hx₂₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x2 i : MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0` using `fun i => constantCoeff_X _`. Establish `hx₃₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x3 i : MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0` using `fun i => constantCoeff_X _`. Establish `hx₁ : ∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.x1 (R` using `_root_.GlobalTheory.Katz.Fr p k) (d := d) i) (_root_.GlobalTheory.Katz.x1 (R := k) i) := fun i => red_X' _`.

Establish `hx₂ : ∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.x2 (R` using `_root_.GlobalTheory.Katz.Fr p k) (d := d) i) (_root_.GlobalTheory.Katz.x2 (R := k) i) := fun i => red_X' _`. Establish `hx₃ : ∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.x3 (R` using `_root_.GlobalTheory.Katz.Fr p k) (d := d) i) (_root_.GlobalTheory.Katz.x3 (R := k) i) := fun i => red_X' _`. Take `⟨h₁₂₀, h₁₂⟩` from `hop _ _ _ _ hx₁₀ hx₂₀ hx₁ hx₂`. Take `⟨h₂₃₀, h₂₃⟩` from `hop _ _ _ _ hx₂₀ hx₃₀ hx₂ hx₃`. Establish `hl₀ : ∀ i, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0` using `fun i => constantCoeff_X _`.

Establish `hr₀ : ∀ i, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0` using `fun i => constantCoeff_X _`. Establish `hl : ∀ i, _root_.GlobalTheory.Katz.Red p (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) (X (Sum.inl i))` using `fun i => red_X' _`. Establish `hr : ∀ i, _root_.GlobalTheory.Katz.Red p (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) (X (Sum.inr i))` using `fun i => red_X' _`. Use `⟨fun g c hg => ⟨?_, ?_⟩, fun b b' hb => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩, fun c g hg => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.Katz.cob2`.

Conclude with `red_sub_divisor (red_add_divisor (red_sub_divisor (red_at2_of_red hx₂₀ hx₃₀ hx₂ hx₃ hg) (red_at2_of_red h₁₂₀ hx₃₀ h₁₂ hx₃ hg)) (red_at2_of_red hx₁₀ h₂₃₀ hx₁ h₂₃ hg)) (red_at2_of_red hx₁₀ hx₂₀ hx₁ hx₂ hg)`. Unfold `_root_.GlobalTheory.Katz.swap`. Conclude with `red_at2_of_red hr₀ hl₀ hr hl hg`. Unfold `_root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR`. Conclude with `red_sub_divisor (red_sub_divisor ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ μ hL₀ hL).1 b b' hb) ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ _ hl₀ hl).1 b b' hb)) ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ _ h …`.

Unfold `_root_.GlobalTheory.Katz.lin _root_.GlobalTheory.Katz.RedV`. Unfold `_root_.GlobalTheory.Katz.Red at hb`. Introduce `i`. Conclude with `hb _`. Conclude with `(hop _ _ _ _ hx₁₀ h₂₃₀ hx₁ h₂₃).2 i`.

Conclude with `(hop _ _ _ _ h₁₂₀ hx₃₀ h₁₂ hx₃).2 i`. Unfold `_root_.GlobalTheory.Katz.cob2`. Conclude with `sub_mem (add_mem (sub_mem (at2_mem_intBy_of_red hx₂₀ hx₃₀ hx₂ hx₃ c hg) (at2_mem_intBy_of_red h₁₂₀ hx₃₀ h₁₂ hx₃ c hg)) (at2_mem_intBy_of_red hx₁₀ h₂₃₀ hx₁ h₂₃ c hg)) (at2_mem_intBy_of_red hx₁₀ hx₂₀ hx₁ hx₂ c hg)`. Unfold `_root_.GlobalTheory.Katz.swap`. Conclude with `at2_mem_intBy_of_red hr₀ hl₀ hr hl c hg`.
-/
theorem _root_.GlobalTheory.Katz.red_coboundaries : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ i, constantCoeff (μ i) = 0) → (∀ g c, _root_.GlobalTheory.Katz.Red p g c → _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob2 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) g) (_root_.GlobalTheory.Katz.cob2 μ c) ∧ _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.swap g) (_root_.GlobalTheory.Katz.swap c)) ∧ (∀ b b', _root_.GlobalTheory.Katz.Red p b b' → _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) b) (_root_.GlobalTheory.Katz.cob1 μ b') ∧ _root_.GlobalTheory.Katz.RedV p (_root_.GlobalTheory.Katz.lin b) (_root_.GlobalTheory.Katz.lin b')) ∧ (∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3) i) (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3) i) ∧ _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3 i) (_root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3 i)) ∧ ∀ (c : WittVector p k) g, g ∈ _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) c → _root_.GlobalTheory.Katz.cob2 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) g ∈ _root_.GlobalTheory.Katz.intBy p k _ c ∧ _root_.GlobalTheory.Katz.swap g ∈ _root_.GlobalTheory.Katz.intBy p k _ c := by
  intro p _ k _ _ _ d μ hμ
  have hL₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.lift p (μ i)) = 0 := fun i =>
    _root_.GlobalTheory.Katz.constantCoeff_lift p (hμ i)
  have hL : ∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.lift p (μ i)) (μ i) :=
    fun i => red_lift_self (μ i)
  have hop : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k))
      (a' b' : Fin d → MvPowerSeries τ k),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      (∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i)) →
      (∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i)) →
      (∀ i, constantCoeff (_root_.GlobalTheory.Katz.op
        (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) a b i) = 0) ∧
      ∀ i, _root_.GlobalTheory.Katz.Red p
        (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) a b i)
        (_root_.GlobalTheory.Katz.op μ a' b' i) := by
    intro τ a b a' b' ha₀ hb₀ ha hb
    exact ⟨fun i => constantCoeff_at2_eq_zero ha₀ hb₀ (hL₀ i),
      fun i => red_at2_of_red ha₀ hb₀ ha hb (hL i)⟩
  have hx₁₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x1 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₂₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x2 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₃₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x3 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₁ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x1 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x1 (R := k) i) := fun i => red_X' _
  have hx₂ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x2 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x2 (R := k) i) := fun i => red_X' _
  have hx₃ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x3 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x3 (R := k) i) := fun i => red_X' _
  obtain ⟨h₁₂₀, h₁₂⟩ := hop _ _ _ _ hx₁₀ hx₂₀ hx₁ hx₂
  obtain ⟨h₂₃₀, h₂₃⟩ := hop _ _ _ _ hx₂₀ hx₃₀ hx₂ hx₃
  have hl₀ : ∀ i, constantCoeff (X (Sum.inl i) :
      MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i => constantCoeff_X _
  have hr₀ : ∀ i, constantCoeff (X (Sum.inr i) :
      MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i => constantCoeff_X _
  have hl : ∀ i, _root_.GlobalTheory.Katz.Red p
      (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k))
      (X (Sum.inl i)) := fun i => red_X' _
  have hr : ∀ i, _root_.GlobalTheory.Katz.Red p
      (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k))
      (X (Sum.inr i)) := fun i => red_X' _
  refine ⟨fun g c hg => ⟨?_, ?_⟩, fun b b' hb => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩,
    fun c g hg => ⟨?_, ?_⟩⟩
  · unfold _root_.GlobalTheory.Katz.cob2
    exact red_sub_divisor (red_add_divisor (red_sub_divisor
      (red_at2_of_red hx₂₀ hx₃₀ hx₂ hx₃ hg)
      (red_at2_of_red h₁₂₀ hx₃₀ h₁₂ hx₃ hg))
      (red_at2_of_red hx₁₀ h₂₃₀ hx₁ h₂₃ hg))
      (red_at2_of_red hx₁₀ hx₂₀ hx₁ hx₂ hg)
  · unfold _root_.GlobalTheory.Katz.swap
    exact red_at2_of_red hr₀ hl₀ hr hl hg
  · unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
    exact red_sub_divisor (red_sub_divisor
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ μ hL₀ hL).1 b b' hb)
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ _ hl₀ hl).1 b b' hb))
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ _ hr₀ hr).1 b b' hb)
  · unfold _root_.GlobalTheory.Katz.lin _root_.GlobalTheory.Katz.RedV
    unfold _root_.GlobalTheory.Katz.Red at hb
    intro i
    exact hb _
  · exact (hop _ _ _ _ hx₁₀ h₂₃₀ hx₁ h₂₃).2 i
  · exact (hop _ _ _ _ h₁₂₀ hx₃₀ h₁₂ hx₃).2 i
  · unfold _root_.GlobalTheory.Katz.cob2
    exact sub_mem (add_mem (sub_mem
      (at2_mem_intBy_of_red hx₂₀ hx₃₀ hx₂ hx₃ c hg)
      (at2_mem_intBy_of_red h₁₂₀ hx₃₀ h₁₂ hx₃ c hg))
      (at2_mem_intBy_of_red hx₁₀ h₂₃₀ hx₁ h₂₃ c hg))
      (at2_mem_intBy_of_red hx₁₀ hx₂₀ hx₁ hx₂ c hg)
  · unfold _root_.GlobalTheory.Katz.swap
    exact at2_mem_intBy_of_red hr₀ hl₀ hr hl c hg
