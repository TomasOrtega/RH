import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic

open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem hnSum_mem_zl (N : Submodule R V) (y : E) :
    y ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = y :=
  Iff.rfl

/- English proof (translation)
Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `(hnSum_mem_zl ρ A y).1 hy`. Conclude with `(hnSum_mem_zl ρ B _).2 ⟨x, h hx, rfl⟩`.
-/
theorem hnSum_zl_mono {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (hnSum_mem_zl ρ A y).1 hy
  exact (hnSum_mem_zl ρ B _).2 ⟨x, h hx, rfl⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `(hnSum_mem_zl ρ _ y).1 hy`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup ((hnSum_mem_zl ρ A _).2 ⟨a, ha, rfl⟩) ((hnSum_mem_zl ρ B _).2 ⟨b, hb, rfl⟩)`. Conclude with `sup_le (hnSum_zl_mono ρ le_sup_left) (hnSum_zl_mono ρ le_sup_right)`.
-/
theorem hnSum_zl_sup (A B : Submodule R V) : zl ρ (A ⊔ B) = zl ρ A ⊔ zl ρ B := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (hnSum_mem_zl ρ _ y).1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup ((hnSum_mem_zl ρ A _).2 ⟨a, ha, rfl⟩)
      ((hnSum_mem_zl ρ B _).2 ⟨b, hb, rfl⟩)
  · exact sup_le (hnSum_zl_mono ρ le_sup_left) (hnSum_zl_mono ρ le_sup_right)

variable [FiniteDimensional ℝ E]

/- English proof (translation)
Use `⟨hL.1.mono h, ?_⟩` and prove the remaining obligations. Use `haveI := hL.2`. Conclude with `DiscreteTopology.of_continuous_injective (f := fun y : zl ρ N => (⟨y.1, hnSum_zl_mono ρ h y.2⟩ : zl ρ L)) (continuous_subtype_val.subtype_mk _) (by`. Introduce `a b hab`. Simplify using `only [Subtype.mk.injEq] at hab`.

Conclude with `Subtype.ext hab)`.
-/
theorem hnSum_isLat_mono {L N : Submodule R V} (hL : IsLat ρ L) (h : N ≤ L) : IsLat ρ N := by
  refine ⟨hL.1.mono h, ?_⟩
  haveI := hL.2
  exact DiscreteTopology.of_continuous_injective
    (f := fun y : zl ρ N => (⟨y.1, hnSum_zl_mono ρ h y.2⟩ : zl ρ L))
    (continuous_subtype_val.subtype_mk _)
    (by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext hab)

/- English proof (translation)
Establish `h0 : ρ x = 0` using `inner_self_eq_zero.1 h`. Conclude with `hA.1 hx A.zero_mem (by rw [h0, map_zero])`.
-/
theorem hnSum_orth_zero {A : Submodule R V} (hA : IsLat ρ A) {x : V} (hx : x ∈ A)
    (h : inner ℝ (ρ x) (ρ x) = 0) : x = 0 := by
  have h0 : ρ x = 0 := inner_self_eq_zero.1 h
  exact hA.1 hx A.zero_mem (by rw [h0, map_zero])

/- English proof (translation)
Establish `horth : ∀ x ∈ zl ρ A, ∀ y ∈ zl ρ B, inner ℝ x y = 0`. Introduce `x hx y hy`. Take `⟨a, ha, rfl⟩` from `(hnSum_mem_zl ρ A x).1 hx`. Take `⟨b, hb, rfl⟩` from `(hnSum_mem_zl ρ B y).1 hy`. Conclude with `h a ha b hb`.

Take `⟨hd, hdeg, -⟩` from `Formalism.F.orthSum E (zl ρ A) (zl ρ B) hA.2 hB.2 horth`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx x' hx' hxx`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 (show x ∈ A ⊔ B from hx)`. Take `⟨a', ha', b', hb', rfl⟩` from `Submodule.mem_sup.1 (show x' ∈ A ⊔ B from hx')`.

Establish `e : ρ (a - a') = ρ (b' - b)`. Rewrite `hxx` using `[map_add, map_add]`. Rewrite using `[map_sub, map_sub, sub_eq_sub_iff_add_eq_add, hxx, add_comm]`. Establish `hu : a - a' = 0`. Apply `hnSum_orth_zero ρ hA (A.sub_mem ha ha')` to reduce the goal to its premises.

Rewrite using `[congrArg (inner ℝ (ρ (a - a'))) e]`. Conclude with `h _ (A.sub_mem ha ha') _ (B.sub_mem hb' hb)`. Establish `hv : b' - b = 0`. Apply `hnSum_orth_zero ρ hB (B.sub_mem hb' hb)` to reduce the goal to its premises. Rewrite using `[← e]`.

Use `nth_rewrite 2 [e]`. Conclude with `h _ (A.sub_mem ha ha') _ (B.sub_mem hb' hb)`. Rewrite using `[sub_eq_zero.1 hu, sub_eq_zero.1 hv]`. Rewrite using `[hnSum_zl_sup]`. Conclude with `hd`.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Conclude with `(Submodule.mem_bot R).2 (hnSum_orth_zero ρ hA hx.1 (h x hx.1 x hx.2))`. Unfold `deg`. Rewrite using `[hnSum_zl_sup]`.

Conclude with `hdeg`.
-/
theorem hnSum_orth {A B : Submodule R V} (hA : IsLat ρ A) (hB : IsLat ρ B)
    (h : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) :
    IsLat ρ (A ⊔ B) ∧ A ⊓ B = ⊥ ∧ deg ρ (A ⊔ B) = deg ρ A + deg ρ B := by
  have horth : ∀ x ∈ zl ρ A, ∀ y ∈ zl ρ B, inner ℝ x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (hnSum_mem_zl ρ A x).1 hx
    obtain ⟨b, hb, rfl⟩ := (hnSum_mem_zl ρ B y).1 hy
    exact h a ha b hb
  obtain ⟨hd, hdeg, -⟩ := Formalism.F.orthSum E (zl ρ A) (zl ρ B) hA.2 hB.2 horth
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x hx x' hx' hxx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (show x ∈ A ⊔ B from hx)
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 (show x' ∈ A ⊔ B from hx')
    have e : ρ (a - a') = ρ (b' - b) := by
      rw [map_add, map_add] at hxx
      rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, hxx, add_comm]
    have hu : a - a' = 0 := by
      apply hnSum_orth_zero ρ hA (A.sub_mem ha ha')
      rw [congrArg (inner ℝ (ρ (a - a'))) e]
      exact h _ (A.sub_mem ha ha') _ (B.sub_mem hb' hb)
    have hv : b' - b = 0 := by
      apply hnSum_orth_zero ρ hB (B.sub_mem hb' hb)
      rw [← e]
      nth_rewrite 2 [e]
      exact h _ (A.sub_mem ha ha') _ (B.sub_mem hb' hb)
    rw [sub_eq_zero.1 hu, sub_eq_zero.1 hv]
  · rw [hnSum_zl_sup]
    exact hd
  · rw [eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot R).2 (hnSum_orth_zero ρ hA hx.1 (h x hx.1 x hx.2))
  · unfold deg
    rw [hnSum_zl_sup]
    exact hdeg

end

universe u v w x

section

variable {R : Type u} {V : Type v} {E : Type w} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)

/- English proof (translation)
Establish `e : zl ρ (⊥ : Submodule R V) = ⊥`. Use extensionality with `y`. Simplify using `[hnSum_mem_zl, eq_comm]`. Unfold `rk Formalism.F.rk`. Rewrite using `[e]`.

Simplify using the standard rewrite rules.
-/
theorem hnSum_rk_bot : rk ρ (⊥ : Submodule R V) = 0 := by
  have e : zl ρ (⊥ : Submodule R V) = ⊥ := by
    ext y
    simp [hnSum_mem_zl, eq_comm]
  unfold rk Formalism.F.rk
  rw [e]
  simp

/- English proof (translation)
Take `⟨hL, hinf, -⟩` from `hnSum_orth ρ hA hB h`. Establish `e` using `(h1 R V E ρ (A ⊔ B) A B hL le_sup_left le_sup_right).1`. Rewrite `e` using `[hinf, hnSum_rk_bot]`. Simplify using `using e`.
-/
theorem hnSum_orth_rk (h1 : DegSupermod.{u, v, w}) {A B : Submodule R V} (hA : IsLat ρ A)
    (hB : IsLat ρ B) (h : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) :
    rk ρ (A ⊔ B) = rk ρ A + rk ρ B := by
  obtain ⟨hL, hinf, -⟩ := hnSum_orth ρ hA hB h
  have e := (h1 R V E ρ (A ⊔ B) A B hL le_sup_left le_sup_right).1
  rw [hinf, hnSum_rk_bot] at e
  simpa using e

/- English proof (translation)
Take `⟨hL, -, -⟩` from `hnSum_orth ρ hA hB h`. Establish `hQ : IsLat ρ (B ⊓ (N ⊔ A))` using `hnSum_isLat_mono ρ hB inf_le_left`. Establish `hAQ : ∀ x ∈ A, ∀ y ∈ B ⊓ (N ⊔ A), inner ℝ (ρ x) (ρ y) = 0` using `fun x hx y hy => h x hx y hy.1`. Establish `hNA : N ⊔ A = A ⊔ B ⊓ (N ⊔ A)`. Rewrite using `[← sup_inf_assoc_of_le B (le_sup_right : A ≤ N ⊔ A)]`.

Conclude with `(inf_eq_right.2 (sup_le hN le_sup_left)).symm`. Establish `s` using `h1 R V E ρ (A ⊔ B) N A hL hN le_sup_left`. Take `⟨-, -, dQ⟩` from `hnSum_orth ρ hA hQ hAQ`. Establish `rQ` using `hnSum_orth_rk ρ h1 hA hQ hAQ`. Rewrite `s` using `[hNA, dQ, rQ]`.

Take `⟨sr, sd⟩` from `s`. Use `⟨by linarith, by omega⟩` and prove the remaining obligations.
-/
theorem hnSum_split (h1 : DegSupermod.{u, v, w}) {A B : Submodule R V} (hA : IsLat ρ A)
    (hB : IsLat ρ B) (h : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) {N : Submodule R V}
    (hN : N ≤ A ⊔ B) :
    deg ρ N ≤ deg ρ (N ⊓ A) + deg ρ (B ⊓ (N ⊔ A)) ∧
      rk ρ N = rk ρ (N ⊓ A) + rk ρ (B ⊓ (N ⊔ A)) := by
  obtain ⟨hL, -, -⟩ := hnSum_orth ρ hA hB h
  have hQ : IsLat ρ (B ⊓ (N ⊔ A)) := hnSum_isLat_mono ρ hB inf_le_left
  have hAQ : ∀ x ∈ A, ∀ y ∈ B ⊓ (N ⊔ A), inner ℝ (ρ x) (ρ y) = 0 :=
    fun x hx y hy => h x hx y hy.1
  have hNA : N ⊔ A = A ⊔ B ⊓ (N ⊔ A) := by
    rw [← sup_inf_assoc_of_le B (le_sup_right : A ≤ N ⊔ A)]
    exact (inf_eq_right.2 (sup_le hN le_sup_left)).symm
  have s := h1 R V E ρ (A ⊔ B) N A hL hN le_sup_left
  obtain ⟨-, -, dQ⟩ := hnSum_orth ρ hA hQ hAQ
  have rQ := hnSum_orth_rk ρ h1 hA hQ hAQ
  rw [hNA, dQ, rQ] at s
  obtain ⟨sr, sd⟩ := s
  refine ⟨by linarith, by omega⟩

end

/- English proof (translation)
Establish `hAl : IsLat ρ A` using `hnSum_isLat_mono ρ hL hA`. Establish `hBl : IsLat ρ B` using `hnSum_isLat_mono ρ hL hB`. Establish `hM : A ⊔ B ≤ L` using `sup_le hA hB`. Establish `hMl : IsLat ρ (A ⊔ B)` using `hnSum_isLat_mono ρ hL hM`. Establish `hM0 : A ⊔ B ≠ ⊥` using `fun e => hA0 (eq_bot_iff.2 ((le_sup_left : A ≤ A ⊔ B).trans e.le))`.

Rewrite using `[(h2 R V E ρ (A ⊔ B) hMl hM0).2.1 θ]`. Introduce `N hN`. Establish `eA` using `((h2 R V E ρ A hAl hA0).2.1 θ).1 hθA (N ⊓ A) inf_le_right`. Establish `eB` using `((h2 R V E ρ B hBl hB0).2.1 θ).1 hθB (B ⊓ (N ⊔ A)) inf_le_left`. Establish `hNA : N ⊔ A ≤ L` using `sup_le (hN.trans hM) hA`.

Establish `s1` using `h1 R V E ρ L N A hL (hN.trans hM) hA`. Establish `s2` using `h1 R V E ρ L B (N ⊔ A) hL hB hNA`. Establish `hBNA : B ⊔ (N ⊔ A) = A ⊔ B` using `le_antisymm (sup_le le_sup_right (sup_le hN le_sup_left)) (sup_le ((le_sup_right : A ≤ N ⊔ A).trans le_sup_right) le_sup_left)`. Rewrite `s2` using `[hBNA]`. Take `⟨r1, d1⟩` from `s1`.

Take `⟨r2, d2⟩` from `s2`. Establish `r1' : (rk ρ (N ⊔ A) : ℝ) + rk ρ (N ⊓ A) = rk ρ N + rk ρ A` using `by exact_mod_cast r1`. Establish `r2' : (rk ρ (A ⊔ B) : ℝ) + rk ρ (B ⊓ (N ⊔ A)) = rk ρ B + rk ρ (N ⊔ A)`. Conclude with `r2` after adjusting the coercions. Establish `key : θ * ((rk ρ (A ⊔ B) : ℝ) - rk ρ N) = θ * ((rk ρ B : ℝ) - rk ρ (B ⊓ (N ⊔ A))) + θ * ((rk ρ A : ℝ) - rk ρ (N ⊓ A))`.

Rewrite using `[← mul_add]`. Use `congr 1`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[key]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem le_muMin_sup_of_le_muMin {R : Type u} {V : Type v} {E : Type w} [Ring R]
    [AddCommGroup V] [Module R V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (ρ : V →+ E)
    {L A B : Submodule R V} (hL : IsLat ρ L) (hA : A ≤ L) (hB : B ≤ L) (hA0 : A ≠ ⊥)
    (hB0 : B ≠ ⊥) {θ : ℝ} (hθA : θ ≤ muMin ρ A) (hθB : θ ≤ muMin ρ B) :
    θ ≤ muMin ρ (A ⊔ B) := by
  have hAl : IsLat ρ A := hnSum_isLat_mono ρ hL hA
  have hBl : IsLat ρ B := hnSum_isLat_mono ρ hL hB
  have hM : A ⊔ B ≤ L := sup_le hA hB
  have hMl : IsLat ρ (A ⊔ B) := hnSum_isLat_mono ρ hL hM
  have hM0 : A ⊔ B ≠ ⊥ := fun e => hA0 (eq_bot_iff.2 ((le_sup_left : A ≤ A ⊔ B).trans e.le))
  rw [(h2 R V E ρ (A ⊔ B) hMl hM0).2.1 θ]
  intro N hN
  have eA := ((h2 R V E ρ A hAl hA0).2.1 θ).1 hθA (N ⊓ A) inf_le_right
  have eB := ((h2 R V E ρ B hBl hB0).2.1 θ).1 hθB (B ⊓ (N ⊔ A)) inf_le_left
  have hNA : N ⊔ A ≤ L := sup_le (hN.trans hM) hA
  have s1 := h1 R V E ρ L N A hL (hN.trans hM) hA
  have s2 := h1 R V E ρ L B (N ⊔ A) hL hB hNA
  have hBNA : B ⊔ (N ⊔ A) = A ⊔ B :=
    le_antisymm (sup_le le_sup_right (sup_le hN le_sup_left))
      (sup_le ((le_sup_right : A ≤ N ⊔ A).trans le_sup_right) le_sup_left)
  rw [hBNA] at s2
  obtain ⟨r1, d1⟩ := s1
  obtain ⟨r2, d2⟩ := s2
  have r1' : (rk ρ (N ⊔ A) : ℝ) + rk ρ (N ⊓ A) = rk ρ N + rk ρ A := by exact_mod_cast r1
  have r2' : (rk ρ (A ⊔ B) : ℝ) + rk ρ (B ⊓ (N ⊔ A)) = rk ρ B + rk ρ (N ⊔ A) := by
    exact_mod_cast r2
  have key : θ * ((rk ρ (A ⊔ B) : ℝ) - rk ρ N) =
      θ * ((rk ρ B : ℝ) - rk ρ (B ⊓ (N ⊔ A))) + θ * ((rk ρ A : ℝ) - rk ρ (N ⊓ A)) := by
    rw [← mul_add]
    congr 1
    linarith
  rw [key]
  linarith

/- English proof (translation)
Establish `hM0 : A ⊔ B ≠ ⊥` using `fun e => hA0 (eq_bot_iff.2 ((le_sup_left : A ≤ A ⊔ B).trans e.le))`. Take `⟨hL, -, dAB⟩` from `hnSum_orth ρ hA hB h`. Establish `rAB` using `hnSum_orth_rk ρ h1 hA hB h`. Rewrite using `[(h2 R V E ρ A hA hA0).2.1]`. Introduce `N hN`.

Establish `hNB : ∀ x ∈ N, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0` using `fun x hx y hy => h x (hN hx) y hy`. Establish `hNl : IsLat ρ N` using `hnSum_isLat_mono ρ hA hN`. Take `⟨-, -, dNB⟩` from `hnSum_orth ρ hNl hB hNB`. Establish `rNB` using `hnSum_orth_rk ρ h1 hNl hB hNB`. Establish `key` using `((h2 R V E ρ (A ⊔ B) hL hM0).2.1 (muMin ρ (A ⊔ B))).1 le_rfl (N ⊔ B) (sup_le_sup_right hN B)`.

Rewrite `key` using `[rNB, rAB, dNB, dAB]`. Move the coercions through the operations in `at key`. Establish `e : (rk ρ A : ℝ) - rk ρ N = ((rk ρ A : ℝ) + rk ρ B) - ((rk ρ N : ℝ) + rk ρ B)` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem muMin_sup_le_muMin_of_orthogonal {R : Type u} {V : Type v} {E : Type w} [Ring R]
    [AddCommGroup V] [Module R V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (ρ : V →+ E)
    {A B : Submodule R V} (hA : IsLat ρ A) (hB : IsLat ρ B)
    (h : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) (hA0 : A ≠ ⊥) :
    muMin ρ (A ⊔ B) ≤ muMin ρ A := by
  have hM0 : A ⊔ B ≠ ⊥ := fun e => hA0 (eq_bot_iff.2 ((le_sup_left : A ≤ A ⊔ B).trans e.le))
  obtain ⟨hL, -, dAB⟩ := hnSum_orth ρ hA hB h
  have rAB := hnSum_orth_rk ρ h1 hA hB h
  rw [(h2 R V E ρ A hA hA0).2.1]
  intro N hN
  have hNB : ∀ x ∈ N, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0 := fun x hx y hy => h x (hN hx) y hy
  have hNl : IsLat ρ N := hnSum_isLat_mono ρ hA hN
  obtain ⟨-, -, dNB⟩ := hnSum_orth ρ hNl hB hNB
  have rNB := hnSum_orth_rk ρ h1 hNl hB hNB
  have key := ((h2 R V E ρ (A ⊔ B) hL hM0).2.1 (muMin ρ (A ⊔ B))).1 le_rfl (N ⊔ B)
    (sup_le_sup_right hN B)
  rw [rNB, rAB, dNB, dAB] at key
  push_cast at key
  have e : (rk ρ A : ℝ) - rk ρ N = ((rk ρ A : ℝ) + rk ρ B) - ((rk ρ N : ℝ) + rk ρ B) := by ring
  rw [e]
  linarith

/- English proof (translation)
Introduce `R V E _ _ _ _ _ _ ρ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `L ι s A θ hL hs hA`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact absurd hs Finset.not_nonempty_empty`.

Consider the case `@insert a s ha ih`. Rewrite using `[Finset.iSup_insert]`. Establish `ha'` using `hA a (Finset.mem_insert_self a s)`. Distinguish the cases in `hs' : s.Nonempty`. Establish `hrest : ∀ i ∈ s, A i ≤ L ∧ A i ≠ ⊥ ∧ θ ≤ muMin ρ (A i)` using `fun i hi => hA i (Finset.mem_insert_of_mem hi)`.

Establish `hle : (⨆ i ∈ s, A i) ≤ L` using `iSup₂_le fun i hi => (hrest i hi).1`. Establish `hne : (⨆ i ∈ s, A i) ≠ ⊥`. Take `⟨j, hj⟩` from `hs'`. Introduce `hb`. Apply `(hrest j hj).2.1` to reduce the goal to its premises.

Conclude with `eq_bot_iff.2 ((le_iSup₂_of_le (f := fun i (_ : i ∈ s) => A i) j hj le_rfl).trans hb.le)`. Conclude with `le_muMin_sup_of_le_muMin h1 h2 ρ hL ha'.1 hle ha'.2.1 hne ha'.2.2 (ih hs' hrest)`. Rewrite using `[Finset.not_nonempty_iff_eq_empty.1 hs']`. Simplify using `using ha'.2.2`. Introduce `A B hA hB h`.

Take `⟨hL, -, hdeg⟩` from `hnSum_orth ρ hA hB h`. Use `⟨hL, hdeg, fun hA0 hB0 => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hM0 : A ⊔ B ≠ ⊥` using `fun e => hA0 (eq_bot_iff.2 ((le_sup_left : A ≤ A ⊔ B).trans e.le))`. Establish `mA` using `(h2 R V E ρ A hA hA0).1`. Establish `mB` using `(h2 R V E ρ B hB hB0).1`.

Establish `mM` using `(h2 R V E ρ (A ⊔ B) hL hM0).1`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[mM]`. Introduce `N hN`. Take `⟨hd, hr⟩` from `hnSum_split ρ h1 hA hB h hN`.

Establish `eA` using `((mA (muMax ρ A)).1 le_rfl) (N ⊓ A) inf_le_right`. Establish `eB` using `((mB (muMax ρ B)).1 le_rfl) (B ⊓ (N ⊔ A)) inf_le_left`. Establish `fA : muMax ρ A * (rk ρ (N ⊓ A) : ℝ) ≤ max (muMax ρ A) (muMax ρ B) * rk ρ (N ⊓ A)` using `mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)`. Establish `fB : muMax ρ B * (rk ρ (B ⊓ (N ⊔ A)) : ℝ) ≤ max (muMax ρ A) (muMax ρ B) * rk ρ (B ⊓ (N ⊔ A))` using `mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)`. Rewrite using `[hr]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `max_le` to reduce the goal to its premises. Rewrite using `[mA]`. Introduce `N hN`.

Conclude with `(mM _).1 le_rfl N (hN.trans le_sup_left)`. Rewrite using `[mB]`. Introduce `N hN`. Conclude with `(mM _).1 le_rfl N (hN.trans le_sup_right)`. Apply `le_antisymm` to reduce the goal to its premises.

Use `le_min (muMin_sup_le_muMin_of_orthogonal h1 h2 ρ hA hB h hA0) ?_` and prove the remaining obligations. Establish `h' : ∀ y ∈ B, ∀ x ∈ A, inner ℝ (ρ y) (ρ x) = 0`. Introduce `y hy x hx`. Rewrite using `[real_inner_comm]`. Conclude with `h x hx y hy`.

Use `muMin_sup_le_muMin_of_orthogonal h1 h2 ρ hB hA h' hB0` as an intermediate fact. Rewrite `this` using `[sup_comm]`. Then use the resulting hypothesis. Conclude with `le_muMin_sup_of_le_muMin h1 h2 ρ hL le_sup_left le_sup_right hA0 hB0 (min_le_left _ _) (min_le_right _ _)`.
-/
theorem hnSum_of (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : SatBasic.{u, v, w}) :
    HNSum.{u, v, w, x} := by
  classical
  intro R V E _ _ _ _ _ _ ρ
  refine ⟨?_, ?_⟩
  · intro L ι s A θ hL hs hA
    induction s using Finset.induction_on with
    | empty => exact absurd hs Finset.not_nonempty_empty
    | @insert a s ha ih =>
      rw [Finset.iSup_insert]
      have ha' := hA a (Finset.mem_insert_self a s)
      by_cases hs' : s.Nonempty
      · have hrest : ∀ i ∈ s, A i ≤ L ∧ A i ≠ ⊥ ∧ θ ≤ muMin ρ (A i) :=
          fun i hi => hA i (Finset.mem_insert_of_mem hi)
        have hle : (⨆ i ∈ s, A i) ≤ L := iSup₂_le fun i hi => (hrest i hi).1
        have hne : (⨆ i ∈ s, A i) ≠ ⊥ := by
          obtain ⟨j, hj⟩ := hs'
          intro hb
          apply (hrest j hj).2.1
          exact eq_bot_iff.2 ((le_iSup₂_of_le (f := fun i (_ : i ∈ s) => A i) j hj le_rfl).trans hb.le)
        exact le_muMin_sup_of_le_muMin h1 h2 ρ hL ha'.1 hle ha'.2.1 hne ha'.2.2 (ih hs' hrest)
      · rw [Finset.not_nonempty_iff_eq_empty.1 hs']
        simpa using ha'.2.2
  · intro A B hA hB h
    obtain ⟨hL, -, hdeg⟩ := hnSum_orth ρ hA hB h
    refine ⟨hL, hdeg, fun hA0 hB0 => ⟨?_, ?_⟩⟩
    · have hM0 : A ⊔ B ≠ ⊥ :=
        fun e => hA0 (eq_bot_iff.2 ((le_sup_left : A ≤ A ⊔ B).trans e.le))
      have mA := (h2 R V E ρ A hA hA0).1
      have mB := (h2 R V E ρ B hB hB0).1
      have mM := (h2 R V E ρ (A ⊔ B) hL hM0).1
      apply le_antisymm
      · rw [mM]
        intro N hN
        obtain ⟨hd, hr⟩ := hnSum_split ρ h1 hA hB h hN
        have eA := ((mA (muMax ρ A)).1 le_rfl) (N ⊓ A) inf_le_right
        have eB := ((mB (muMax ρ B)).1 le_rfl) (B ⊓ (N ⊔ A)) inf_le_left
        have fA : muMax ρ A * (rk ρ (N ⊓ A) : ℝ) ≤ max (muMax ρ A) (muMax ρ B) * rk ρ (N ⊓ A) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
        have fB : muMax ρ B * (rk ρ (B ⊓ (N ⊔ A)) : ℝ) ≤
            max (muMax ρ A) (muMax ρ B) * rk ρ (B ⊓ (N ⊔ A)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)
        rw [hr]
        push_cast
        linarith
      · apply max_le
        · rw [mA]
          intro N hN
          exact (mM _).1 le_rfl N (hN.trans le_sup_left)
        · rw [mB]
          intro N hN
          exact (mM _).1 le_rfl N (hN.trans le_sup_right)
    · apply le_antisymm
      · refine le_min (muMin_sup_le_muMin_of_orthogonal h1 h2 ρ hA hB h hA0) ?_
        have h' : ∀ y ∈ B, ∀ x ∈ A, inner ℝ (ρ y) (ρ x) = 0 := by
          intro y hy x hx
          rw [real_inner_comm]
          exact h x hx y hy
        have := muMin_sup_le_muMin_of_orthogonal h1 h2 ρ hB hA h' hB0
        rwa [sup_comm] at this
      · exact le_muMin_sup_of_le_muMin h1 h2 ρ hL le_sup_left le_sup_right hA0 hB0
          (min_le_left _ _) (min_le_right _ _)

/- English proof (translation)
The claim follows from `hnSum_of degree_supermodular slope_characterization saturation_basic_properties`.
-/
theorem polygon_slope_sum : HNSum :=
  hnSum_of degree_supermodular slope_characterization saturation_basic_properties

end Formalism.HN
