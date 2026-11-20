import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLeMaximalIdealPowSmulOfDirected
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

/- English proof (translation)
Rewrite using `[Subalgebra.coe_add, RatModel.val_add (RatModel.gPt_specializes hy.1) F.2 G.2]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`.
-/
theorem norm_val_add_le {U : Set M.Z} {x : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hy : M.Cen U x y)
    (F G : M.O x) :
    ‖M.val (gPt p ≫ y) ((F + G : M.O x) : Ω)‖ ≤ max ‖M.val (gPt p ≫ y) (F : Ω)‖ ‖M.val (gPt p ≫ y) (G : Ω)‖ := by
  rw [Subalgebra.coe_add, RatModel.val_add (RatModel.gPt_specializes hy.1) F.2 G.2]
  exact IsUltrametricDist.norm_add_le_max _ _

/- English proof (translation)
Rewrite using `[Subalgebra.coe_mul, RatModel.val_mul (RatModel.gPt_specializes hy.1) c.2 F.2, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hy.norm_val_le_one c.2)`.
-/
theorem norm_val_mul_le {U : Set M.Z} {x : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hy : M.Cen U x y)
    (c F : M.O x) : ‖M.val (gPt p ≫ y) ((c * F : M.O x) : Ω)‖ ≤ ‖M.val (gPt p ≫ y) (F : Ω)‖ := by
  rw [Subalgebra.coe_mul, RatModel.val_mul (RatModel.gPt_specializes hy.1) c.2 F.2, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hy.norm_val_le_one c.2)

def smallIdeal (U : M.Z.Opens) (x : M.Z) (f : Ω) (N : ℕ) : Ideal (M.O x) where
  carrier := {F | ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y →
      ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨
        ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ N}
  zero_mem' := by
    intro p _ y _
    left
    have h0 : ((0 : M.O x) : Ω) = 0 := rfl
    rw [h0, RatModel.val_zero, norm_zero]
    exact norm_nonneg _
  add_mem' := by
    intro F G hF hG p _ y hy
    have h := norm_val_add_le M hy F G
    rcases le_total ‖M.val (gPt p ≫ y) (F : Ω)‖ ‖M.val (gPt p ≫ y) (G : Ω)‖ with hle | hle
    · rw [max_eq_right hle] at h
      rcases hG p y hy with h' | ⟨k, hk, h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨k, hk, h.trans h'⟩
    · rw [max_eq_left hle] at h
      rcases hF p y hy with h' | ⟨k, hk, h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨k, hk, h.trans h'⟩
  smul_mem' := by
    intro c F hF p _ y hy
    have h := norm_val_mul_le M hy c F
    rcases hF p y hy with h' | ⟨k, hk, h'⟩
    · exact Or.inl (h.trans h')
    · exact Or.inr ⟨k, hk, h.trans h'⟩

variable {M}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_smallIdeal {U : M.Z.Opens} {x : M.Z} {f : Ω} {N : ℕ} {F : M.O x} :
    F ∈ smallIdeal M U x f N ↔ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y →
      ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨
        ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ N := Iff.rfl

/- English proof (translation)
Introduce `N N' hN F hF p _ y hy`. Break down `hF p y hy with h' | ⟨k, hk, h'⟩` into its components or cases. Conclude with `Or.inl h'`. Use `Or.inr ⟨k, hk, h'.trans (pow_le_pow_of_le_one (norm_nonneg _) (hy.norm_val_le_one hk.1) hN)⟩` and prove the remaining obligations.
-/
theorem smallIdeal_antitone (U : M.Z.Opens) (x : M.Z) (f : Ω) : Antitone (smallIdeal M U x f) := by
  intro N N' hN F hF p _ y hy
  rcases hF p y hy with h' | ⟨k, hk, h'⟩
  · exact Or.inl h'
  · refine Or.inr ⟨k, hk, h'.trans (pow_le_pow_of_le_one (norm_nonneg _) (hy.norm_val_le_one hk.1) hN)⟩

/- English proof (translation)
Introduce `_ _ _ _` and use `Or.inl le_rfl`.
-/
theorem self_mem_smallIdeal (U : M.Z.Opens) {x : M.Z} {f : Ω} (hf : f ∈ M.O x) (N : ℕ) :
    (⟨f, hf⟩ : M.O x) ∈ smallIdeal M U x f N :=
  fun _ _ _ _ => Or.inl le_rfl

end GlobalTheory.Izumi

namespace GlobalTheory.Izumi

open IsLocalRing

/- English proof (translation)
Use `set B := AdicCompletion (maximalIdeal A) A`. Use `set φ := algebraMap A B`. Use `haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _`. Use `set I : Ideal B := Ideal.span {φ f}`. Set `L : ℕ → Submodule B (B ⧸ I)` to `fun N => Submodule.map I.mkQ ((K N).map φ)`.

Establish `hL : Directed (· ≥ ·) L`. Use `Antitone.directed_ge fun N N' hN => ?_` and prove the remaining obligations. Conclude with `Submodule.map_mono (Ideal.map_mono (hK hN))`. Establish `hIK : ∀ N, I ≤ (K N).map φ` using `fun N => (Ideal.span_le).2 (Set.singleton_subset_iff.2 (Ideal.mem_map_of_mem φ (hf N)))`. Establish `h0 : (⨅ N, L N) = ⊥`.

Use `eq_bot_iff.2 fun x hx => ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `I.mkQ_surjective x`. Establish `hb : b ∈ ⨅ N, (K N).map φ`. Use `Submodule.mem_iInf _ |>.2 fun N => ?_` and prove the remaining obligations. Take `⟨b', hb', hbb'⟩` from `(Submodule.mem_iInf _).1 hx N`.

Establish `hd : b' - b ∈ I`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]`. Simplify using `only [Submodule.mkQ_apply] at hbb'`. Rewrite using `[hbb', sub_self]`. Use `Submodule.sub_mem _ hb' (hIK N hd)` as an intermediate fact.

Simplify using `using this`. Use `h hb` as an intermediate fact. Simplify using `only [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `this`. Take `⟨N, hN⟩` from `GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ I) ℕ L inferInstance hL h0 e`.

Use `⟨N, fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1 : I.mkQ (φ a) ∈ maximalIdeal B ^ e • (⊤ : Submodule B (B ⧸ I))` using `hN (Submodule.mem_map_of_mem (Ideal.mem_map_of_mem φ ha))`. Establish `h2 : maximalIdeal B ^ e • (⊤ : Submodule B (B ⧸ I)) = Submodule.map I.mkQ (maximalIdeal B ^ e)`. Establish `h4 : maximalIdeal B ^ e • (⊤ : Submodule B B) = maximalIdeal B ^ e`. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top]`.

Rewrite using `[← Submodule.range_mkQ I, ← Submodule.map_top, ← Submodule.map_smul'', h4]`. Rewrite `h1` using `[h2, ← Submodule.mem_comap, Submodule.comap_map_mkQ]`. Take `⟨u, hu, t, ht, hut⟩` from `Submodule.mem_sup.1 h1`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hu`. Use `set ψ := AdicCompletion.evalₐ (maximalIdeal A) (R := A) e`.

Establish `hψ : ∀ r : A, ψ (φ r) = Ideal.Quotient.mk _ r` using `fun r => ψ.commutes r`. Establish `ht0 : ψ t = 0`. Establish `hle : maximalIdeal B ^ e ≤ RingHom.ker ψ.toRingHom`. Rewrite using `[AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]`. Introduce `r hr`.

Simplify using `only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]`. Rewrite using `[hψ, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hr`. Conclude with `hle ht`. Take `⟨c', hc'⟩` from `Ideal.Quotient.mk_surjective (ψ c)`.

Establish `h3` using `congrArg ψ hut`. Rewrite `h3` using `[map_add, map_mul, ht0, add_zero, hψ, hψ, ← hc', ← map_mul, Ideal.Quotient.eq]`. Establish `: a = c' * f + (a - c' * f)` using `by ring`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)) (by rw [← neg_sub]; exact neg_mem h3)`.
-/
theorem exists_le_span_sup_pow (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A)
    (f : A) (hK : Antitone K) (hf : ∀ N, f ∈ K N)
    (h : ⨅ N, (K N).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) ≤
      Ideal.span {algebraMap A (AdicCompletion (maximalIdeal A) A) f}) (e : ℕ) :
    ∃ N, K N ≤ Ideal.span {f} ⊔ maximalIdeal A ^ e := by
  set B := AdicCompletion (maximalIdeal A) A
  set φ := algebraMap A B
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  set I : Ideal B := Ideal.span {φ f}
  let L : ℕ → Submodule B (B ⧸ I) := fun N => Submodule.map I.mkQ ((K N).map φ)
  have hL : Directed (· ≥ ·) L := by
    refine Antitone.directed_ge fun N N' hN => ?_
    exact Submodule.map_mono (Ideal.map_mono (hK hN))
  have hIK : ∀ N, I ≤ (K N).map φ := fun N =>
    (Ideal.span_le).2 (Set.singleton_subset_iff.2 (Ideal.mem_map_of_mem φ (hf N)))
  have h0 : (⨅ N, L N) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨b, rfl⟩ := I.mkQ_surjective x
    have hb : b ∈ ⨅ N, (K N).map φ := by
      refine Submodule.mem_iInf _ |>.2 fun N => ?_
      obtain ⟨b', hb', hbb'⟩ := (Submodule.mem_iInf _).1 hx N
      have hd : b' - b ∈ I := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
        simp only [Submodule.mkQ_apply] at hbb'
        rw [hbb', sub_self]
      have := Submodule.sub_mem _ hb' (hIK N hd)
      simpa using this
    have := h hb
    simp only [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact this
  obtain ⟨N, hN⟩ := GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ I) ℕ L
    inferInstance hL h0 e
  refine ⟨N, fun a ha => ?_⟩
  have h1 : I.mkQ (φ a) ∈ maximalIdeal B ^ e • (⊤ : Submodule B (B ⧸ I)) :=
    hN (Submodule.mem_map_of_mem (Ideal.mem_map_of_mem φ ha))
  have h2 : maximalIdeal B ^ e • (⊤ : Submodule B (B ⧸ I)) = Submodule.map I.mkQ (maximalIdeal B ^ e) := by
    have h4 : maximalIdeal B ^ e • (⊤ : Submodule B B) = maximalIdeal B ^ e := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [← Submodule.range_mkQ I, ← Submodule.map_top, ← Submodule.map_smul'', h4]
  rw [h2, ← Submodule.mem_comap, Submodule.comap_map_mkQ] at h1
  obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  set ψ := AdicCompletion.evalₐ (maximalIdeal A) (R := A) e
  have hψ : ∀ r : A, ψ (φ r) = Ideal.Quotient.mk _ r := fun r => ψ.commutes r
  have ht0 : ψ t = 0 := by
    have hle : maximalIdeal B ^ e ≤ RingHom.ker ψ.toRingHom := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [hψ, Ideal.Quotient.eq_zero_iff_mem]
      exact hr
    exact hle ht
  obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (ψ c)
  have h3 := congrArg ψ hut
  rw [map_add, map_mul, ht0, add_zero, hψ, hψ, ← hc', ← map_mul, Ideal.Quotient.eq] at h3
  have : a = c' * f + (a - c' * f) := by ring
  rw [this]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)) (by rw [← neg_sub]; exact neg_mem h3)

end GlobalTheory.Izumi
