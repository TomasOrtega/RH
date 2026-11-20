import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumSubspaceStabilizerMulBlockFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardSubspacesMulGeneralLinearGroupCardStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassEqOfLinearEquivInvariantStatement

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL.MassMult

open Classical in

/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_fintype, ← Fintype.sum_subtype_add_sum_subtype p]`. Establish `h1 : ∑ i : {x // ¬ p x}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = 0` using `Finset.sum_eq_zero fun i _ => dif_neg i.2`. Rewrite using `[h1, add_zero]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [dif_pos i.2]`.
-/
theorem finsum_subtype_dite {α : Type} [Fintype α] (p : α → Prop) (f : {x // p x} → ℂ) :
    ∑ᶠ x, f x = ∑ x, if h : p x then f ⟨x, h⟩ else 0 := by
  rw [finsum_eq_sum_of_fintype, ← Fintype.sum_subtype_add_sum_subtype p]
  have h1 : ∑ i : {x // ¬ p x}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => dif_neg i.2
  rw [h1, add_zero]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.2]

open Classical in

/- English proof (translation)
Unfold `mass`. Use `finsum_congr fun g => ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_if]`. Both sides reduce to the same expression.
-/
theorem mass_eq {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (φ : Module.End F V → ℂ) (P : F[X]) :
    mass φ P = ∑ᶠ g, if LinearMap.charpoly g = P then φ g else 0 := by
  unfold mass
  refine finsum_congr fun g => ?_
  rw [finsum_eq_if]
  rfl

/- English proof (translation)
Establish `h : {g : F[X] | g.Monic ∧ g ∣ P}.Finite`. Use `Polynomial.fintypeSubtypeMonicDvd P hP.ne_zero` as an intermediate fact. Conclude with `Set.finite_coe_iff.mp (Finite.of_fintype {g : F[X] // g.Monic ∧ g ∣ P})`. Use `(h.prod h).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨h1, h2, h3⟩`.

Conclude with `⟨⟨h1, h3 ▸ dvd_mul_right _ _⟩, ⟨h2, h3 ▸ dvd_mul_left _ _⟩⟩`.
-/
theorem finite_pairs {F : Type} [Field F] (P : F[X]) (hP : P.Monic) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  have h : {g : F[X] | g.Monic ∧ g ∣ P}.Finite := by
    have := Polynomial.fintypeSubtypeMonicDvd P hP.ne_zero
    exact Set.finite_coe_iff.mp (Finite.of_fintype {g : F[X] // g.Monic ∧ g ∣ P})
  refine (h.prod h).subset ?_
  rintro x ⟨h1, h2, h3⟩
  exact ⟨⟨h1, h3 ▸ dvd_mul_right _ _⟩, ⟨h2, h3 ▸ dvd_mul_left _ _⟩⟩

/- English proof (translation)
The claim follows from `Module.finite_of_finite F`.
-/
theorem finite_end (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] : Finite (Module.End F V) :=
  Module.finite_of_finite F

/- English proof (translation)
Rewrite using `[mass_eq]`. Use `finsum_eq_zero_of_forall_eq_zero fun g => if_neg ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `h (LinearMap.charpoly_natDegree g).symm`.
-/
theorem mass_eq_zero {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (φ : Module.End F V → ℂ) (P : F[X]) (h : Module.finrank F V ≠ P.natDegree) : mass φ P = 0 := by
  rw [mass_eq]
  refine finsum_eq_zero_of_forall_eq_zero fun g => if_neg ?_
  rintro rfl
  exact h (LinearMap.charpoly_natDegree g).symm

open Classical in

/- English proof (translation)
Distinguish the cases in `hg : c = P`. Rewrite using `[if_pos hg, Finset.sum_eq_single (a, b)]`. Rewrite using `[if_pos rfl, if_pos rfl, mul_one]`. Introduce and unpack `⟨b1, b2⟩ _ hb`. Distinguish the cases in `h1 : a = b1`.

Distinguish the cases in `h2 : b = b2`. Conclude with `absurd (by rw [h1, h2]) hb`. Rewrite using `[if_neg h2, mul_zero]`. Rewrite using `[if_neg h1, zero_mul]`. Introduce `hn`.

Conclude with `(hn ((hT (a, b)).2 ⟨ha, hb, hc.symm.trans hg⟩)).elim`. Rewrite using `[if_neg hg]`. Use `(Finset.sum_eq_zero ?_).symm` and prove the remaining obligations. Introduce and unpack `⟨b1, b2⟩ hb`. Distinguish the cases in `h1 : a = b1`.

Distinguish the cases in `h2 : b = b2`. Use `absurd ?_ hg` and prove the remaining obligations. Rewrite using `[hc, h1, h2]`. Conclude with `((hT (b1, b2)).1 hb).2.2`. Rewrite using `[if_neg h2, mul_zero]`.

Rewrite using `[if_neg h1, zero_mul]`.
-/
theorem indicator_split {F : Type} [Field F] (P : F[X])
    (T : Finset (F[X] × F[X])) (hT : ∀ x, x ∈ T ↔ x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P)
    {a b c : F[X]} (ha : a.Monic) (hb : b.Monic) (hc : c = a * b) (z : ℂ) :
    (if c = P then z else 0) =
      ∑ x ∈ T, (if a = x.1 then z else 0) * (if b = x.2 then (1 : ℂ) else 0) := by
  by_cases hg : c = P
  · rw [if_pos hg, Finset.sum_eq_single (a, b)]
    · rw [if_pos rfl, if_pos rfl, mul_one]
    · rintro ⟨b1, b2⟩ _ hb
      by_cases h1 : a = b1
      · by_cases h2 : b = b2
        · exact absurd (by rw [h1, h2]) hb
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro hn
      exact (hn ((hT (a, b)).2 ⟨ha, hb, hc.symm.trans hg⟩)).elim
  · rw [if_neg hg]
    refine (Finset.sum_eq_zero ?_).symm
    rintro ⟨b1, b2⟩ hb
    by_cases h1 : a = b1
    · by_cases h2 : b = b2
      · refine absurd ?_ hg
        rw [hc, h1, h2]
        exact ((hT (b1, b2)).1 hb).2.2
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

open Classical in

/- English proof (translation)
Use `finite_end F V` as an intermediate fact. Use `Fintype.ofFinite {g : Module.End F V // ∀ x ∈ W, g x ∈ W}` as an intermediate fact. Establish `key : ∀ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W}, (if LinearMap.charpoly g.1 = P then φ (g.1.restrict g.2) else 0) = ∑ x ∈ T, (if LinearMap.charpoly (g.1.restrict g.2) = x.1 then φ (g.1.restrict g.2) else 0) * (if LinearMap.charpoly (W.mapQ W g.1 (fun x hx => g.2 x hx)) = x.2 …`. Introduce `g`. Establish `hc` using `(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V W g.1 g.2).1`.

Conclude with `indicator_split P T hT (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _) hc _`. Rewrite using `[finsum_congr key, finsum_eq_sum_of_fintype, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[mass_eq, mass_eq, ← finsum_eq_sum_of_fintype]`. Conclude with `GlobalTheory.T.finsum_subspaceStabilizer_mul_block_functions F V W (fun a => if LinearMap.charpoly a = x.1 then φ a else 0) (fun b => if LinearMap.charpoly b = x.2 then (1 : ℂ) else 0)`.
-/
theorem stab_sum (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W : Submodule F V) (φ : Module.End F W → ℂ) (P : F[X])
    (T : Finset (F[X] × F[X])) (hT : ∀ x, x ∈ T ↔ x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P) :
    ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
        (if LinearMap.charpoly g.1 = P then φ (g.1.restrict g.2) else 0) =
      ∑ x ∈ T, (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) *
        (mass φ x.1 * mass (fun _ : Module.End F (V ⧸ W) => (1 : ℂ)) x.2) := by
  have := finite_end F V
  have := Fintype.ofFinite {g : Module.End F V // ∀ x ∈ W, g x ∈ W}
  have key : ∀ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
      (if LinearMap.charpoly g.1 = P then φ (g.1.restrict g.2) else 0) =
      ∑ x ∈ T, (if LinearMap.charpoly (g.1.restrict g.2) = x.1 then φ (g.1.restrict g.2) else 0) *
        (if LinearMap.charpoly (W.mapQ W g.1 (fun x hx => g.2 x hx)) = x.2 then (1 : ℂ) else 0) := by
    intro g
    have hc := (GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V W g.1 g.2).1
    exact indicator_split P T hT (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _) hc _
  rw [finsum_congr key, finsum_eq_sum_of_fintype, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mass_eq, mass_eq, ← finsum_eq_sum_of_fintype]
  exact GlobalTheory.T.finsum_subspaceStabilizer_mul_block_functions F V W (fun a => if LinearMap.charpoly a = x.1 then φ a else 0)
    (fun b => if LinearMap.charpoly b = x.2 then (1 : ℂ) else 0)

/- English proof (translation)
Unfold `glCard`. Conclude with `(Nat.card_pos (α := GL (Fin n) F)).ne'` after adjusting the coercions.
-/
theorem glCard_ne_zero (F : Type) [Field F] [Finite F] (n : ℕ) : glCard F n ≠ 0 := by
  unfold glCard
  exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'

/- English proof (translation)
Introduce `F _ _ V _ _ _ Φ hΦ P hP hdeg`. Use `finite_end F V` as an intermediate fact. Establish `: Finite V` using `Module.finite_of_finite F`. Use `Fintype.ofFinite (Module.End F V)` as an intermediate fact. Use `Fintype.ofFinite (Submodule F V)` as an intermediate fact.

Establish `hfin` using `finite_pairs P hP`. Establish `hT : ∀ x, x ∈ hfin.toFinset ↔ x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P` using `fun x => by`. Rewrite using `[Set.Finite.mem_toFinset]`. Both sides reduce to the same expression. Establish `h1 : mass (fun g : Module.End F V => ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, Φ W.1 (g.restrict W.2)) P = ∑ W : Submodule F V, ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W}, (if LinearMap.charpoly g.1 = P then Φ W (g.1.restrict g.2) else 0)`.

Rewrite using `[mass_eq, finsum_eq_sum_of_fintype]`. Simplify using `only [finsum_subtype_dite]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Distinguish the cases in `hg : LinearMap.charpoly g = P`.

Simplify using `only [if_pos hg]`. Simplify using `only [if_neg hg, dite_eq_ite, ite_self, Finset.sum_const_zero]`. Rewrite using `[h1, conv, finsum_mem_eq_finite_toFinset_sum _ hfin]`. Simplify using `only [fun W : Submodule F V => stab_sum F V W (Φ W) P _ hT]`. Rewrite using `[Finset.sum_comm, Finset.sum_div]`.

Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce and unpack `⟨D, E⟩ hx`. Take `⟨hD, hE, hDE⟩` from `(hT _).1 hx`. Simplify using `only at hD hE hDE ⊢`. Establish `hsum : D.natDegree + E.natDegree = Module.finrank F V`.

Rewrite using `[← hdeg, ← hDE, hD.natDegree_mul hE]`. Establish `h2 : ∀ W : Submodule F V, (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) * (mass (Φ W) D * mass (fun _ : Module.End F (V ⧸ W) => (1 : ℂ)) E) = if Module.finrank F W = D.natDegree then (Nat.card F : ℂ) ^ (D.natDegree * E.natDegree) * (mass (Φ (Fin D.natDegree → …`. Introduce `W`. Distinguish the cases in `hW : Module.finrank F W = D.natDegree`. Establish `hq : Module.finrank F (V ⧸ W) = E.natDegree`.

Use `Submodule.finrank_quotient_add_finrank W` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos hW, GlobalTheory.T.endomorphismMass_eq_of_linearEquiv_invariant F W Φ hΦ D hW.symm, GlobalTheory.T.endomorphismMass_eq_of_linearEquiv_invariant F (V ⧸ W) (fun _ _ _ _ _ => (1 : ℂ)) (fun _ _ _ _ _ _ _ _ _ _ => rfl) E hq.symm, hW, hq]`. Rewrite using `[if_neg hW, mass_eq_zero _ _ hW, zero_mul, mul_zero]`. Establish `h3` using `GlobalTheory.T.card_subspaces_mul_generalLinearGroupCard F V D.natDegree (by omega)`.

Establish `h4 : Module.finrank F V - D.natDegree = E.natDegree` using `by omega`. Rewrite `h3` using `[h4, Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = D.natDegree}), Fintype.card_subtype]`. Rewrite using `[Finset.sum_congr rfl fun W _ => h2 W, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hdeg, mu]`. Establish `g1` using `glCard_ne_zero F D.natDegree`. Establish `g2` using `glCard_ne_zero F E.natDegree`.

Establish `g3` using `glCard_ne_zero F (Module.finrank F V)`. Rewrite using `[div_mul_div_comm, div_eq_div_iff g3 (mul_ne_zero g1 g2), ← h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mass_mult : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V → mass (fun g : Module.End F V => ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, Φ W.1 (g.restrict W.2)) P / glCard F P.natDegree = conv (fun D => mass (Φ (Fin D.natDegree → F)) D / glCard F D.natDegree) mu P := by
  classical
  intro F _ _ V _ _ _ Φ hΦ P hP hdeg
  have := finite_end F V
  have : Finite V := Module.finite_of_finite F
  have := Fintype.ofFinite (Module.End F V)
  have := Fintype.ofFinite (Submodule F V)
  have hfin := finite_pairs P hP
  have hT : ∀ x, x ∈ hfin.toFinset ↔ x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P := fun x => by
    rw [Set.Finite.mem_toFinset]; rfl
  have h1 : mass (fun g : Module.End F V => ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W},
      Φ W.1 (g.restrict W.2)) P = ∑ W : Submodule F V,
      ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
        (if LinearMap.charpoly g.1 = P then Φ W (g.1.restrict g.2) else 0) := by
    rw [mass_eq, finsum_eq_sum_of_fintype]
    simp only [finsum_subtype_dite]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : LinearMap.charpoly g = P
    · simp only [if_pos hg]
    · simp only [if_neg hg, dite_eq_ite, ite_self, Finset.sum_const_zero]
  rw [h1, conv, finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp only [fun W : Submodule F V => stab_sum F V W (Φ W) P _ hT]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  rintro ⟨D, E⟩ hx
  obtain ⟨hD, hE, hDE⟩ := (hT _).1 hx
  simp only at hD hE hDE ⊢
  have hsum : D.natDegree + E.natDegree = Module.finrank F V := by
    rw [← hdeg, ← hDE, hD.natDegree_mul hE]
  have h2 : ∀ W : Submodule F V, (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) *
      (mass (Φ W) D * mass (fun _ : Module.End F (V ⧸ W) => (1 : ℂ)) E) =
      if Module.finrank F W = D.natDegree then (Nat.card F : ℂ) ^ (D.natDegree * E.natDegree) *
        (mass (Φ (Fin D.natDegree → F)) D *
          mass (fun _ : Module.End F (Fin E.natDegree → F) => (1 : ℂ)) E) else 0 := by
    intro W
    by_cases hW : Module.finrank F W = D.natDegree
    · have hq : Module.finrank F (V ⧸ W) = E.natDegree := by
        have := Submodule.finrank_quotient_add_finrank W
        omega
      rw [if_pos hW, GlobalTheory.T.endomorphismMass_eq_of_linearEquiv_invariant F W Φ hΦ D hW.symm,
        GlobalTheory.T.endomorphismMass_eq_of_linearEquiv_invariant F (V ⧸ W) (fun _ _ _ _ _ => (1 : ℂ)) (fun _ _ _ _ _ _ _ _ _ _ => rfl) E hq.symm,
        hW, hq]
    · rw [if_neg hW, mass_eq_zero _ _ hW, zero_mul, mul_zero]
  have h3 := GlobalTheory.T.card_subspaces_mul_generalLinearGroupCard F V D.natDegree (by omega)
  have h4 : Module.finrank F V - D.natDegree = E.natDegree := by omega
  rw [h4, Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = D.natDegree}),
    Fintype.card_subtype] at h3
  rw [Finset.sum_congr rfl fun W _ => h2 W, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hdeg, mu]
  have g1 := glCard_ne_zero F D.natDegree
  have g2 := glCard_ne_zero F E.natDegree
  have g3 := glCard_ne_zero F (Module.finrank F V)
  rw [div_mul_div_comm, div_eq_div_iff g3 (mul_ne_zero g1 g2), ← h3]
  ring

end GlobalTheory.CuspGL.MassMult
