import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH Sesq altE IsSelfDual IsHerm IsPosDef IsLat IsReps IsSemiChar imgLat Th alphaQ opU
  relIdx inter fixedBy stdH stdLat blk4 pow4 slice tens4 kernel4 sumU IsIsom F0 StdData TripleData tripleMu)
open Formalism.L2.Th1.GD (LocNorm)

namespace ImageLatticeRepresentatives

section Reps

variable {V : Type} [AddCommGroup V]

/- English proof (translation)
Unfold `relIdx AddSubgroup.relIndex AddSubgroup.index`. Set `f : S → (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂)` to `fun x => QuotientAddGroup.mk ⟨x.1, hS.1 x.1 x.2⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩ ⟨y, hy⟩ hxy`.

Establish `h1` using `(QuotientAddGroup.eq).1 hxy`. Rewrite `h1` using `[AddSubgroup.mem_addSubgroupOf]`. Establish `h2 : x - y ∈ Λ₁`. Use `Λ₁.neg_mem h1` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg, add_comm]`.

Conclude with `Subtype.ext (hS.2.1 x hx y hy h2)`. Introduce `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H z`. Take `⟨x, hx, hzx⟩` from `hS.2.2 z.1 z.2`.

Use `⟨⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Apply `(QuotientAddGroup.eq).2` to reduce the goal to its premises. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Simplify `hzx` using `[sub_eq_add_neg, add_comm]`. Rewrite using `[← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_coe]`.
-/
theorem relIdx_eq_card {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) :
    relIdx Λ₁ Λ₂ = S.card := by
  unfold relIdx AddSubgroup.relIndex AddSubgroup.index
  let f : S → (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := fun x => QuotientAddGroup.mk ⟨x.1, hS.1 x.1 x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have h1 := (QuotientAddGroup.eq).1 hxy
      rw [AddSubgroup.mem_addSubgroupOf] at h1
      have h2 : x - y ∈ Λ₁ := by
        have := Λ₁.neg_mem h1
        simpa [sub_eq_add_neg, add_comm] using this
      exact Subtype.ext (hS.2.1 x hx y hy h2)
    · intro q
      induction q using QuotientAddGroup.induction_on with
      | H z =>
        obtain ⟨x, hx, hzx⟩ := hS.2.2 z.1 z.2
        refine ⟨⟨x, hx⟩, ?_⟩
        apply (QuotientAddGroup.eq).2
        rw [AddSubgroup.mem_addSubgroupOf]
        simpa [sub_eq_add_neg, add_comm] using hzx
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_coe]

/- English proof (translation)
Use `⟨fun x hx => by rw [he x hx]; exact h.1 x hx, fun x hx y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[he _ (Λ.add_mem hx hy), he x hx, he y hy]`. Conclude with `h.2 x hx y hy`.
-/
theorem semiChar_congr [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α α' : V → ℂ} (h : IsSemiChar H Λ α)
    (he : ∀ x ∈ Λ, α' x = α x) : IsSemiChar H Λ α' := by
  refine ⟨fun x hx => by rw [he x hx]; exact h.1 x hx, fun x hx y hy => ?_⟩
  rw [he _ (Λ.add_mem hx hy), he x hx, he y hy]
  exact h.2 x hx y hy

/- English proof (translation)
Introduce `hdvd`. Establish `hc : relIdx A C = Nat.card (C ⧸ A.addSubgroupOf C)` using `rfl`. Establish `hfin : Finite (C ⧸ A.addSubgroupOf C)` using `Nat.finite_of_card_ne_zero (hc ▸ hAC)`. Take `⟨q, hq⟩` from `exists_prime_addOrderOf_dvd_card' (G := C ⧸ A.addSubgroupOf C) p (hc ▸ hdvd)`. Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective q`.

Establish `h1 : relIdx B C • (y : V) ∈ B` using `AddSubgroup.nsmul_relIndex_mem B y.2`. Establish `h2 : relIdx A B • (relIdx B C • (y : V)) ∈ A` using `AddSubgroup.nsmul_relIndex_mem A h1`. Establish `h3 : (relIdx A B * relIdx B C) • (QuotientAddGroup.mk y : C ⧸ A.addSubgroupOf C) = 0`. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul, mul_smul]`. Conclude with `h2`.

Establish `h4` using `addOrderOf_dvd_of_nsmul_eq_zero h3`. Rewrite `h4` using `[hq]`. Break down `(Nat.Prime.dvd_mul hp.out).1 h4 with h | h` into its components or cases. Conclude with `hAB h`. Conclude with `hBC h`.
-/
theorem not_dvd_relIdx {A B C : AddSubgroup V} (p : ℕ) [hp : Fact p.Prime]
    (hAB : ¬ p ∣ relIdx A B) (hBC : ¬ p ∣ relIdx B C) (hAC : relIdx A C ≠ 0) : ¬ p ∣ relIdx A C := by
  intro hdvd
  have hc : relIdx A C = Nat.card (C ⧸ A.addSubgroupOf C) := rfl
  have hfin : Finite (C ⧸ A.addSubgroupOf C) := Nat.finite_of_card_ne_zero (hc ▸ hAC)
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' (G := C ⧸ A.addSubgroupOf C) p (hc ▸ hdvd)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  have h1 : relIdx B C • (y : V) ∈ B := AddSubgroup.nsmul_relIndex_mem B y.2
  have h2 : relIdx A B • (relIdx B C • (y : V)) ∈ A := AddSubgroup.nsmul_relIndex_mem A h1
  have h3 : (relIdx A B * relIdx B C) • (QuotientAddGroup.mk y : C ⧸ A.addSubgroupOf C) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
      AddSubgroup.coe_nsmul, mul_smul]
    exact h2
  have h4 := addOrderOf_dvd_of_nsmul_eq_zero h3
  rw [hq] at h4
  rcases (Nat.Prime.dvd_mul hp.out).1 h4 with h | h
  · exact hAB h
  · exact hBC h

end Reps

section Isom

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Simplify using `only [imgLat, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `using hx`. Introduce `h`.

Conclude with `⟨g.symm y, h, by simp⟩`.
-/
theorem mem_imgLat (g : V ≃ₗ[ℂ] W) (Λ : AddSubgroup V) (y : W) :
    y ∈ imgLat (g : V →ₗ[ℂ] W) Λ ↔ g.symm y ∈ Λ := by
  simp only [imgLat, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨g.symm y, h, by simp⟩

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.1 hx`. Rewrite using `[mem_imgLat]`. Simplify using `using hS.1 s hs`.

Introduce `x hx y hy hxy`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hy`. Rewrite `hxy` using `[mem_imgLat, ← map_sub]`. Simplify using `only [LinearEquiv.symm_apply_apply] at hxy`.

Rewrite using `[hS.2.1 s hs t ht hxy]`. Introduce `y hy`. Rewrite `hy` using `[mem_imgLat]`. Take `⟨s, hs, hys⟩` from `hS.2.2 _ hy`. Use `⟨g s, Finset.mem_image_of_mem _ hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_imgLat, map_sub]`. Simplify using `using hys`.
-/
theorem isReps_img (g : V ≃ₗ[ℂ] W) {A B : AddSubgroup V} {S : Finset V} (hS : IsReps A B S) [DecidableEq W] :
    IsReps (imgLat (g : V →ₗ[ℂ] W) A) (imgLat (g : V →ₗ[ℂ] W) B) (S.image g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
    rw [mem_imgLat]
    simpa using hS.1 s hs
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    rw [mem_imgLat, ← map_sub] at hxy
    simp only [LinearEquiv.symm_apply_apply] at hxy
    rw [hS.2.1 s hs t ht hxy]
  · intro y hy
    rw [mem_imgLat] at hy
    obtain ⟨s, hs, hys⟩ := hS.2.2 _ hy
    refine ⟨g s, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [mem_imgLat, map_sub]
    simpa using hys

/- English proof (translation)
Take `⟨S, hS⟩` from `(Formalism.L2.Th1.H.repsExist _ A B hAB).1`. Establish `hS'` using `isReps_img g hS`. Establish `hmem : ∀ (Λ : AddSubgroup V) (x : V), x ∈ Λ → g x ∈ imgLat (g : V →ₗ[ℂ] W) Λ`. Introduce `Λ x hx`. Rewrite using `[mem_imgLat, LinearEquiv.symm_apply_apply]`.

Conclude with `hx`. Establish `hαV : IsSemiChar H B (fun x => α' (g x))`. Use `⟨fun x hx => hα'.1 _ (hmem B x hx), fun x hx y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `hα'.2 _ (hmem B x hx) _ (hmem B y hy)`. Establish `h2 : altE H' (g x) (g y) = altE H x y`.

Simplify using `only [altE]`. Rewrite using `[show H' (g x) (g y) = H x y from hg x y]`. Simplify using `only [map_add]`. Rewrite using `[h1, h2]`. Establish `hGV : (fun v => G (g v)) ∈ fixedBy H (fun x => α' (g x)) A`.

Introduce `x hx z`. Establish `hI` using `Formalism.L2.Th1.H.opUIsom V W H H' (g : V →ₗ[ℂ] W) hg x G z`. Simplify using `only [LinearEquiv.coe_coe] at hI`. Simplify using `only`. Rewrite using `[hI]`.

Conclude with `hG _ (hmem A x hx) (g z)`. Rewrite using `[Formalism.L2.Th1.H.interReps _ _ hH _ _ _ hαV _ hGV _ hS z, Formalism.L2.Th1.H.interReps _ _ hH' _ _ _ hα' _ hG _ hS' (g z), relIdx_eq_card hS, relIdx_eq_card hS', Finset.card_image_of_injective _ g.injective]`. Use `congr 1`. Simplify using `only [sumU]`. Rewrite using `[Finset.sum_image (fun x _ y _ hxy => g.injective hxy)]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Establish `hI` using `Formalism.L2.Th1.H.opUIsom V W H H' (g : V →ₗ[ℂ] W) hg x G z`. Simplify using `only [LinearEquiv.coe_coe] at hI`. Rewrite using `[hI]`.
-/
theorem inter_isom (H : Sesq V) (H' : Sesq W) (hH : IsHerm H) (hH' : IsHerm H') (g : V ≃ₗ[ℂ] W)
    (hg : IsIsom H H' (g : V →ₗ[ℂ] W)) (α' : W → ℂ) (A B : AddSubgroup V)
    (hα' : IsSemiChar H' (imgLat (g : V →ₗ[ℂ] W) B) α') (hAB : relIdx A B ≠ 0)
    (G : W → ℂ) (hG : G ∈ fixedBy H' α' (imgLat (g : V →ₗ[ℂ] W) A)) (z : V) :
    inter H (fun x => α' (g x)) A B (fun v => G (g v)) z =
      inter H' α' (imgLat (g : V →ₗ[ℂ] W) A) (imgLat (g : V →ₗ[ℂ] W) B) G (g z) := by
  classical
  obtain ⟨S, hS⟩ := (Formalism.L2.Th1.H.repsExist _ A B hAB).1
  have hS' := isReps_img g hS
  have hmem : ∀ (Λ : AddSubgroup V) (x : V), x ∈ Λ → g x ∈ imgLat (g : V →ₗ[ℂ] W) Λ := by
    intro Λ x hx
    rw [mem_imgLat, LinearEquiv.symm_apply_apply]; exact hx
  have hαV : IsSemiChar H B (fun x => α' (g x)) := by
    refine ⟨fun x hx => hα'.1 _ (hmem B x hx), fun x hx y hy => ?_⟩
    have h1 := hα'.2 _ (hmem B x hx) _ (hmem B y hy)
    have h2 : altE H' (g x) (g y) = altE H x y := by
      simp only [altE]; rw [show H' (g x) (g y) = H x y from hg x y]
    simp only [map_add]
    rw [h1, h2]
  have hGV : (fun v => G (g v)) ∈ fixedBy H (fun x => α' (g x)) A := by
    intro x hx z
    have hI := Formalism.L2.Th1.H.opUIsom V W H H' (g : V →ₗ[ℂ] W) hg x G z
    simp only [LinearEquiv.coe_coe] at hI
    simp only
    rw [hI]
    exact hG _ (hmem A x hx) (g z)
  rw [Formalism.L2.Th1.H.interReps _ _ hH _ _ _ hαV _ hGV _ hS z,
    Formalism.L2.Th1.H.interReps _ _ hH' _ _ _ hα' _ hG _ hS' (g z),
    relIdx_eq_card hS, relIdx_eq_card hS', Finset.card_image_of_injective _ g.injective]
  congr 1
  simp only [sumU]
  rw [Finset.sum_image (fun x _ y _ hxy => g.injective hxy)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hI := Formalism.L2.Th1.H.opUIsom V W H H' (g : V →ₗ[ℂ] W) hg x G z
  simp only [LinearEquiv.coe_coe] at hI
  rw [hI]

end Isom

section Tens

variable {n : Type} [Fintype n] [DecidableEq n]

def asm (x : Fin 4 → n → ℂ) : Fin 4 × n → ℂ := fun w => x w.1 w.2

/- English proof (translation)
Introduce `x y h`. Use function extensionality and compare the values at `a i`. Conclude with `congrFun h (a, i)`.
-/
theorem asm_injective : Function.Injective (asm (n := n)) := by
  intro x y h
  funext a i
  exact congrFun h (a, i)

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz a`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hz`. Rewrite `hx` using `[Fintype.mem_piFinset]`. Conclude with `hS.1 _ (hx a)`.

Introduce `z hz z' hz' hzz`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hz`. Take `⟨x', hx', rfl⟩` from `Finset.mem_image.1 hz'`. Rewrite `hx`, `hx'` using `[Fintype.mem_piFinset]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Conclude with `hS.2.1 _ (hx a) _ (hx' a) (hzz a)`. Introduce `y hy choose s hs hys using fun a => hS.2.2 (slice a y) (hy a)`. Conclude with `⟨asm s, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hs), fun a => hys a⟩`.
-/
theorem representatives_fourth_power {Λ₁ Λ₂ : AddSubgroup (n → ℂ)} {S : Finset (n → ℂ)} (hS : IsReps Λ₁ Λ₂ S) :
    IsReps (pow4 Λ₁) (pow4 Λ₂) ((Fintype.piFinset fun _ : Fin 4 => S).image asm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz a
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    rw [Fintype.mem_piFinset] at hx
    exact hS.1 _ (hx a)
  · intro z hz z' hz' hzz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hz'
    rw [Fintype.mem_piFinset] at hx hx'
    congr 1
    funext a
    exact hS.2.1 _ (hx a) _ (hx' a) (hzz a)
  · intro y hy
    choose s hs hys using fun a => hS.2.2 (slice a y) (hy a)
    exact ⟨asm s, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hs), fun a => hys a⟩

/- English proof (translation)
Establish `hfin : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂)` using `Nat.finite_of_card_ne_zero h12`. Use `letI := Fintype.ofFinite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂)`. Set `S : Finset (n → ℂ)` to `Finset.univ.image fun q : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ => ((Quotient.out q : Λ₂) : n → ℂ)`. Establish `hS : IsReps Λ₁ Λ₂ S`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `(Quotient.out q).2`. Introduce `x hx y hy hxy`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hx`.

Take `⟨q', -, rfl⟩` from `Finset.mem_image.1 hy`. Establish `hq : q = q'`. Rewrite using `[← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']`. Apply `(QuotientAddGroup.eq).2` to reduce the goal to its premises. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`.

Use `Λ₁.neg_mem hxy` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg, add_comm]`. Rewrite using `[hq]`. Introduce `y hy`. Set `q : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂` to `QuotientAddGroup.mk ⟨y, hy⟩`.

Use `⟨((Quotient.out q : Λ₂) : n → ℂ), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩` and prove the remaining obligations. Establish `h1 : (QuotientAddGroup.mk (Quotient.out q) : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) = QuotientAddGroup.mk ⟨y, hy⟩` using `QuotientAddGroup.out_eq' q`. Establish `h2` using `(QuotientAddGroup.eq).1 h1`. Rewrite `h2` using `[AddSubgroup.mem_addSubgroupOf]`. Simplify `h2` using `[sub_eq_add_neg, add_comm]`.

Rewrite using `[relIdx_eq_card (representatives_fourth_power hS), relIdx_eq_card hS, Finset.card_image_of_injective _ asm_injective, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem relative_index_fourth_power {Λ₁ Λ₂ : AddSubgroup (n → ℂ)} (h12 : relIdx Λ₁ Λ₂ ≠ 0) :
    relIdx (pow4 Λ₁) (pow4 Λ₂) = relIdx Λ₁ Λ₂ ^ 4 := by
  classical
  have hfin : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero h12
  letI := Fintype.ofFinite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂)
  let S : Finset (n → ℂ) := Finset.univ.image fun q : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ => ((Quotient.out q : Λ₂) : n → ℂ)
  have hS : IsReps Λ₁ Λ₂ S := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
      exact (Quotient.out q).2
    · intro x hx y hy hxy
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy
      have hq : q = q' := by
        rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
        apply (QuotientAddGroup.eq).2
        rw [AddSubgroup.mem_addSubgroupOf]
        have := Λ₁.neg_mem hxy
        simpa [sub_eq_add_neg, add_comm] using this
      rw [hq]
    · intro y hy
      let q : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ := QuotientAddGroup.mk ⟨y, hy⟩
      refine ⟨((Quotient.out q : Λ₂) : n → ℂ), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
      have h1 : (QuotientAddGroup.mk (Quotient.out q) : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) = QuotientAddGroup.mk ⟨y, hy⟩ :=
        QuotientAddGroup.out_eq' q
      have h2 := (QuotientAddGroup.eq).1 h1
      rw [AddSubgroup.mem_addSubgroupOf] at h2
      simpa [sub_eq_add_neg, add_comm] using h2
  rw [relIdx_eq_card (representatives_fourth_power hS), relIdx_eq_card hS,
    Finset.card_image_of_injective _ asm_injective, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/- English proof (translation)
Establish `key : matH (blk4 h) x y = ∑ a, matH h (slice a x) (slice a y)`. Simplify using `only [matH, LinearMap.mk₂'ₛₗ_apply, blk4, slice]`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single a]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules. Simplify using `only [altE, key, Complex.im_sum]`.
-/
theorem alternating_form_fourth_block (h : Matrix n n ℂ) (x y : Fin 4 × n → ℂ) :
    altE (matH (blk4 h)) x y = ∑ a, altE (matH h) (slice a x) (slice a y) := by
  have key : matH (blk4 h) x y = ∑ a, matH h (slice a x) (slice a y) := by
    simp only [matH, LinearMap.mk₂'ₛₗ_apply, blk4, slice]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simp only [altE, key, Complex.im_sum]

/- English proof (translation)
Establish `key : ∀ x y : Fin 4 × n → ℂ, matH (blk4 h) x y = ∑ a, matH h (slice a x) (slice a y)`. Introduce `x y`. Simplify using `only [matH, LinearMap.mk₂'ₛₗ_apply, blk4, slice]`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.

Introduce `x y`. Rewrite using `[key, key, map_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => hH _ _`.
-/
theorem hermitian_fourth_block (h : Matrix n n ℂ) (hH : IsHerm (matH h)) : IsHerm (matH (blk4 h)) := by
  have key : ∀ x y : Fin 4 × n → ℂ, matH (blk4 h) x y = ∑ a, matH h (slice a x) (slice a y) := by
    intro x y
    simp only [matH, LinearMap.mk₂'ₛₗ_apply, blk4, slice]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  intro x y
  rw [key, key, map_sum]
  exact Finset.sum_congr rfl fun a _ => hH _ _

/- English proof (translation)
Use `⟨fun x hx => ?_, fun x hx y hy => ?_⟩` and prove the remaining obligations. Use `Finset.prod_induction _ (fun z => z = 1 ∨ z = -1) ?_ (Or.inl rfl) (fun a _ => hα.1 _ (hx a))` and prove the remaining obligations. Apply the tactic sequence `rintro u v (rfl | rfl) (rfl | rfl) <;> simp`. Establish `e1 : ∀ a, α (slice a (x + y)) = α (slice a x) * α (slice a y) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (matH h) (slice a x) (slice a y) : ℂ))` using `fun a => hα.2 _ (hx a) _ (hy a)`. Simplify using `only [e1, Finset.prod_mul_distrib]`.

Rewrite using `[alternating_form_fourth_block]`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Complex.exp_sum]`.
-/
theorem semicharacter_fourth_power (h : Matrix n n ℂ) {Λ : AddSubgroup (n → ℂ)} {α : (n → ℂ) → ℂ}
    (hα : IsSemiChar (matH h) Λ α) :
    IsSemiChar (matH (blk4 h)) (pow4 Λ) (fun x => ∏ a, α (slice a x)) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · refine Finset.prod_induction _ (fun z => z = 1 ∨ z = -1) ?_ (Or.inl rfl) (fun a _ => hα.1 _ (hx a))
    rintro u v (rfl | rfl) (rfl | rfl) <;> simp
  · have e1 : ∀ a, α (slice a (x + y)) = α (slice a x) * α (slice a y) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (matH h) (slice a x) (slice a y) : ℂ)) :=
      fun a => hα.2 _ (hx a) _ (hy a)
    simp only [e1, Finset.prod_mul_distrib]
    rw [alternating_form_fourth_block]
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]

/- English proof (translation)
Establish `h1 : Real.sqrt ((r ^ 4 : ℕ) : ℝ) = (Real.sqrt r) ^ 4`. Rewrite using `[show ((r ^ 4 : ℕ) : ℝ) = ((r : ℝ) ^ 2) ^ 2 by push_cast; ring, Real.sqrt_sq (by positivity), show (Real.sqrt r) ^ 4 = ((Real.sqrt r) ^ 2) ^ 2 by ring, Real.sq_sqrt (by positivity)]`. Rewrite using `[h1]`. Use `push_cast`. Rewrite using `[inv_pow]`.
-/
theorem sqrt_fourth_power_inv (r : ℕ) :
    ((Real.sqrt ((r ^ 4 : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ = (((Real.sqrt r : ℝ) : ℂ)⁻¹) ^ 4 := by
  have h1 : Real.sqrt ((r ^ 4 : ℕ) : ℝ) = (Real.sqrt r) ^ 4 := by
    rw [show ((r ^ 4 : ℕ) : ℝ) = ((r : ℝ) ^ 2) ^ 2 by push_cast; ring, Real.sqrt_sq (by positivity),
      show (Real.sqrt r) ^ 4 = ((Real.sqrt r) ^ 2) ^ 2 by ring, Real.sq_sqrt (by positivity)]
  rw [h1]
  push_cast
  rw [inv_pow]

/- English proof (translation)
Take `⟨S, hS⟩` from `(Formalism.L2.Th1.H.repsExist _ Λ₁ Λ₂ h12).1`. Establish `hS4` using `representatives_fourth_power hS`. Establish `hH4 : IsHerm (matH (blk4 h))` using `hermitian_fourth_block h hH`. Establish `hfix4 : tens4 θ ∈ fixedBy (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ₁)` using `(Formalism.L2.Th1.H.tens4Mem n h Λ₁ α (fun _ => θ) (fun _ => hθ)).2`. Use function extensionality and compare the values at `z`.

Establish `eL : tens4 (inter (matH h) α Λ₁ Λ₂ θ) z = (((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹) ^ 4 * ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => S), ∏ a, (α (p a) * opU (matH h) (p a) θ (slice a z))`. Simplify using `only [tens4, Formalism.L2.Th1.H.interReps _ _ hH Λ₁ Λ₂ α hα θ hθ.2 S hS, sumU]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_univ_sum]`. Establish `eR : inter (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ₁) (pow4 Λ₂) (tens4 θ) z = (((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹) ^ 4 * ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => S), ∏ a, (α (p a) * opU (matH h) (p a) θ (slice a z))`. Rewrite using `[Formalism.L2.Th1.H.interReps _ _ hH4 _ _ _ (semicharacter_fourth_power h hα) _ hfix4 _ hS4 z, relative_index_fourth_power h12, sqrt_fourth_power_inv]`.

Use `congr 1`. Simplify using `only [sumU]`. Rewrite using `[Finset.sum_image (fun x _ y _ hxy => asm_injective hxy)]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib]`.

Use `congr 1`. Conclude with `(Formalism.L2.Th1.H.opUBlk4 n h).2 (asm p) (fun _ => θ) z`. Rewrite using `[eL, eR]`.
-/
theorem fourth_tensor_intertwiner (h : Matrix n n ℂ) (hH : IsHerm (matH h)) (Λ₁ Λ₂ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ)
    (hα : IsSemiChar (matH h) Λ₂ α) (h12 : relIdx Λ₁ Λ₂ ≠ 0) (θ : (n → ℂ) → ℂ) (hθ : θ ∈ Th (matH h) α Λ₁) :
    tens4 (inter (matH h) α Λ₁ Λ₂ θ) =
      inter (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ₁) (pow4 Λ₂) (tens4 θ) := by
  classical
  obtain ⟨S, hS⟩ := (Formalism.L2.Th1.H.repsExist _ Λ₁ Λ₂ h12).1
  have hS4 := representatives_fourth_power hS
  have hH4 : IsHerm (matH (blk4 h)) := hermitian_fourth_block h hH
  have hfix4 : tens4 θ ∈ fixedBy (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ₁) :=
    (Formalism.L2.Th1.H.tens4Mem n h Λ₁ α (fun _ => θ) (fun _ => hθ)).2
  funext z
  have eL : tens4 (inter (matH h) α Λ₁ Λ₂ θ) z = (((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹) ^ 4 *
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => S), ∏ a, (α (p a) * opU (matH h) (p a) θ (slice a z)) := by
    simp only [tens4, Formalism.L2.Th1.H.interReps _ _ hH Λ₁ Λ₂ α hα θ hθ.2 S hS, sumU]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_univ_sum]
  have eR : inter (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ₁) (pow4 Λ₂) (tens4 θ) z =
      (((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹) ^ 4 *
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => S), ∏ a, (α (p a) * opU (matH h) (p a) θ (slice a z)) := by
    rw [Formalism.L2.Th1.H.interReps _ _ hH4 _ _ _ (semicharacter_fourth_power h hα) _ hfix4 _ hS4 z, relative_index_fourth_power h12, sqrt_fourth_power_inv]
    congr 1
    simp only [sumU]
    rw [Finset.sum_image (fun x _ y _ hxy => asm_injective hxy)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_mul_distrib]
    congr 1
    exact (Formalism.L2.Th1.H.opUBlk4 n h).2 (asm p) (fun _ => θ) z
  rw [eL, eR]

end Tens

/- English proof (translation)
Break down `Int.even_or_odd b with ⟨k, hk⟩ | h` into its components or cases. It suffices to derive a contradiction. Substitute `hk` using the available equality. Establish `h4 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k)` using `by linear_combination (-1 : ℤ) * hOK.1`. Take `⟨m, hm⟩ : ∃ m : ℤ, (d : ℤ) = 4 * m` from `⟨_, h4⟩`.

Establish `h7` using `hOK.2.2.1`. Use linear arithmetic over natural numbers and integers. Conclude with `h`.
-/
theorem odd_b {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) : Odd b := by
  rcases Int.even_or_odd b with ⟨k, hk⟩ | h
  · exfalso
    subst hk
    have h4 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by linear_combination (-1 : ℤ) * hOK.1
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (d : ℤ) = 4 * m := ⟨_, h4⟩
    have h7 := hOK.2.2.1
    omega
  · exact h

end ImageLatticeRepresentatives

open ImageLatticeRepresentatives

/- English proof (translation)
Introduce `a₀ b₀ c₀ dK ha hdK lam hlam hcm n _ _ h Λ₁ Λ₂ hH _ _ _ hSD₁ hSD₂ hSt₁ hSt₂ θ hθ p _ ι h12 h21 hp12 hLN`. Take `⟨g₁, ε, hI, hidx, hidx2, hε, htens⟩` from `hLN`. Establish `hαs₂ : IsSemiChar (matH h) Λ₂ (alphaQ (Real.sqrt dK / 2) (matH h))` using `(Formalism.L2.Th1.H.alphaQSemi _ (matH h) hH b₀ dK (odd_b hcm) Λ₂ (le_of_eq hSD₂.symm) hSt₂).2.2`. Establish `htens1` using `fourth_tensor_intertwiner h hH Λ₁ Λ₂ _ hαs₂ h12 θ hθ`. Establish `hBC : relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) = relIdx Λ₁ Λ₂ ^ 4`.

Rewrite using `[← relative_index_fourth_power h12]`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ g₁.injective`. Establish `hCB : relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) = relIdx Λ₂ Λ₁ ^ 4`. Rewrite using `[← relative_index_fourth_power h21]`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ g₁.injective`.

Establish `hBC0 : relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) ≠ 0`. Rewrite using `[hBC]`. Conclude with `pow_ne_zero _ h12`. Establish `hCB0 : relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) ≠ 0`. Rewrite using `[hCB]`.

Conclude with `pow_ne_zero _ h21`. Establish `hstdB0 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) ≠ 0`. Introduce `h0`. Conclude with `hidx (h0 ▸ dvd_zero p)`. Establish `hstdC0 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) ≠ 0` using `AddSubgroup.relIndex_ne_zero_trans hstdB0 hBC0`.

Establish `hCstd0 : relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) ≠ 0` using `AddSubgroup.relIndex_ne_zero_trans hCB0 hidx2`. Establish `hpBC : ¬ p ∣ relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂))`. Rewrite using `[hBC]`. Introduce `hd`. Conclude with `hp12 ((Fact.out : p.Prime).dvd_of_dvd_pow hd)`.

Establish `hpC` using `not_dvd_relIdx p hidx hpBC hstdC0`. Establish `hD1` using `Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ₁ g₁ hI hSD₁ hSt₁ hstdB0 hidx2`. Establish `hD2` using `Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ₂ g₁ hI hSD₂ hSt₂ hstdC0 hCstd0`. Establish `hSH` using `Formalism.L2.Th1.H.stdHBasic (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)`. Establish `hF0` using `Formalism.L2.Th1.H.product_theta_mem' (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) (Fin 4 × n) hD1.per hD1.half _ hD1.betaStd`.

Establish `hscStd : IsSemiChar (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)))` using `semiChar_congr (Formalism.L2.Th1.H.stdSemiChar (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) (Fin 4 × n) hD1.per) hD1.betaStd`. Establish `hK1fix` using `Formalism.L2.Th1.H.interFixed _ _ hSH.2.1 _ _ _ hD1.betaSemi hstdB0 _ hF0.1.2`. Establish `hTD : TripleData (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) (imgLat (g₁ : (Fin …` using `{ herm := hSH.2.1 sd₁ := Formalism.L2.Th1.H.stdSelfDual _ _ sd₂ := hD1.selfDual sd₃ := hD2.selfDual sc₁ := hscStd sc₂ := hD1.betaSemi sc₃ := hD2.betaSemi i₁₂ := hstdB0 i₂₁ := hidx2 i₁₃ := hstdC0 i₃₁ := hCstd0 i₂₃ := hBC0 i₃₂ := hCB0 }`. Take `⟨S₂, hS₂⟩` from `(Formalism.L2.Th1.H.repsExist _ _ _ hstdB0).1`. Take `⟨S₃, hS₃⟩` from `(Formalism.L2.Th1.H.repsExist _ _ _ hBC0).1`.

Establish `hF0ne : F0 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) (Fin 4 × n) ≠ 0`. Introduce `h0`. Establish `h1` using `congrFun h0 0`. Rewrite `h1` using `[hF0.2]`. Conclude with `one_ne_zero h1`.

Establish `hμ8` using `Formalism.L2.Th1.H.tripleEighth _ _ _ _ _ _ hTD ⟨_, hF0.1.2, hF0ne⟩ S₂ S₃ hS₂ hS₃`. Establish `hμn : ‖ι (tripleMu (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) (imgLat (g₁ : (Fi …`. Rewrite using `[← pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (8 : ℕ) ≠ 0), ← norm_pow, ← map_pow, hμ8, map_one, norm_one]`. Establish `hα4 : (fun x => ∏ a, alphaQ (Real.sqrt dK / 2) (matH h) (slice a x)) = fun x => alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ x)`. Use function extensionality and compare the values at `x`.

Conclude with `(hD1.betaAlpha x).symm`. Take `⟨μ, hμ⟩ : ∃ μ, tripleMu (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) (imgLat (g₁ …` from `⟨_, rfl⟩`. Rewrite `hμn` using `[hμ]`. Use `⟨g₁, ε * μ, hI, hpC, hCstd0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, norm_mul, hμn, mul_one]`.

Conclude with `hε`. Use function extensionality and compare the values at `z`. Rewrite using `[htens1, htens, Formalism.L2.Th1.H.Inv.inter_smul, hα4]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Establish `hT` using `inter_isom _ _ (hermitian_fourth_block h hH) hSH.2.1 g₁ hI _ (pow4 Λ₁) (pow4 Λ₂) hD2.betaSemi (by rw [relative_index_fourth_power h12]; exact pow_ne_zero _ h12) _ hK1fix z`.

Establish `hTr` using `Formalism.L2.Th1.H.tripleFormula _ _ _ _ _ _ hTD S₂ S₃ hS₂ hS₃ _ hF0.1.2 (g₁ z)`. Rewrite `hTr` using `[hμ]`. Unfold `kernel4`. Rewrite using `[hT, hTr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem local_norm_intertwiner : LocNormInter := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcm n _ _ h Λ₁ Λ₂ hH _ _ _ hSD₁ hSD₂ hSt₁ hSt₂ θ hθ p _ ι h12 h21 hp12 hLN
  classical
  obtain ⟨g₁, ε, hI, hidx, hidx2, hε, htens⟩ := hLN

  have hαs₂ : IsSemiChar (matH h) Λ₂ (alphaQ (Real.sqrt dK / 2) (matH h)) :=
    (Formalism.L2.Th1.H.alphaQSemi _ (matH h) hH b₀ dK (odd_b hcm) Λ₂ (le_of_eq hSD₂.symm) hSt₂).2.2
  have htens1 := fourth_tensor_intertwiner h hH Λ₁ Λ₂ _ hαs₂ h12 θ hθ

  have hBC : relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) = relIdx Λ₁ Λ₂ ^ 4 := by
    rw [← relative_index_fourth_power h12]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ g₁.injective
  have hCB : relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) = relIdx Λ₂ Λ₁ ^ 4 := by
    rw [← relative_index_fourth_power h21]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ g₁.injective
  have hBC0 : relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) ≠ 0 := by
    rw [hBC]; exact pow_ne_zero _ h12
  have hCB0 : relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) ≠ 0 := by
    rw [hCB]; exact pow_ne_zero _ h21
  have hstdB0 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁)) ≠ 0 := by
    intro h0; exact hidx (h0 ▸ dvd_zero p)
  have hstdC0 : relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) ≠ 0 :=
    AddSubgroup.relIndex_ne_zero_trans hstdB0 hBC0
  have hCstd0 : relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂))
      (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) ≠ 0 :=
    AddSubgroup.relIndex_ne_zero_trans hCB0 hidx2
  have hpBC : ¬ p ∣ relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) := by
    rw [hBC]; intro hd; exact hp12 ((Fact.out : p.Prime).dvd_of_dvd_pow hd)
  have hpC := not_dvd_relIdx p hidx hpBC hstdC0

  have hD1 := Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ₁ g₁ hI hSD₁ hSt₁
    hstdB0 hidx2
  have hD2 := Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ₂ g₁ hI hSD₂ hSt₂
    hstdC0 hCstd0
  have hSH := Formalism.L2.Th1.H.stdHBasic (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)
  have hF0 := Formalism.L2.Th1.H.product_theta_mem' (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) (Fin 4 × n) hD1.per hD1.half _ hD1.betaStd
  have hscStd : IsSemiChar (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) :=
    semiChar_congr (Formalism.L2.Th1.H.stdSemiChar (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) (Fin 4 × n) hD1.per)
      hD1.betaStd
  have hK1fix := Formalism.L2.Th1.H.interFixed _ _ hSH.2.1 _ _ _ hD1.betaSemi hstdB0 _ hF0.1.2

  have hTD : TripleData (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)))
      (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) :=
    { herm := hSH.2.1
      sd₁ := Formalism.L2.Th1.H.stdSelfDual _ _
      sd₂ := hD1.selfDual
      sd₃ := hD2.selfDual
      sc₁ := hscStd
      sc₂ := hD1.betaSemi
      sc₃ := hD2.betaSemi
      i₁₂ := hstdB0
      i₂₁ := hidx2
      i₁₃ := hstdC0
      i₃₁ := hCstd0
      i₂₃ := hBC0
      i₃₂ := hCB0 }
  obtain ⟨S₂, hS₂⟩ := (Formalism.L2.Th1.H.repsExist _ _ _ hstdB0).1
  obtain ⟨S₃, hS₃⟩ := (Formalism.L2.Th1.H.repsExist _ _ _ hBC0).1
  have hF0ne : F0 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) (Fin 4 × n) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 0
    rw [hF0.2] at h1
    exact one_ne_zero h1
  have hμ8 := Formalism.L2.Th1.H.tripleEighth _ _ _ _ _ _ hTD ⟨_, hF0.1.2, hF0ne⟩ S₂ S₃ hS₂ hS₃
  have hμn : ‖ι (tripleMu (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)))
      (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) S₂ S₃)‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (8 : ℕ) ≠ 0), ← norm_pow, ← map_pow, hμ8,
      map_one, norm_one]
  have hα4 : (fun x => ∏ a, alphaQ (Real.sqrt dK / 2) (matH h) (slice a x)) =
      fun x => alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ x) := by
    funext x; exact (hD1.betaAlpha x).symm
  obtain ⟨μ, hμ⟩ : ∃ μ, tripleMu (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)))
      (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₁))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ₂)) S₂ S₃ = μ := ⟨_, rfl⟩
  rw [hμ] at hμn
  refine ⟨g₁, ε * μ, hI, hpC, hCstd0, ?_, ?_⟩
  · rw [map_mul, norm_mul, hμn, mul_one]; exact hε
  · funext z
    rw [htens1, htens, Formalism.L2.Th1.H.Inv.inter_smul, hα4]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hT := inter_isom _ _ (hermitian_fourth_block h hH) hSH.2.1 g₁ hI _ (pow4 Λ₁) (pow4 Λ₂) hD2.betaSemi
      (by rw [relative_index_fourth_power h12]; exact pow_ne_zero _ h12) _ hK1fix z
    have hTr := Formalism.L2.Th1.H.tripleFormula _ _ _ _ _ _ hTD S₂ S₃ hS₂ hS₃ _ hF0.1.2 (g₁ z)
    rw [hμ] at hTr
    unfold kernel4
    rw [hT, hTr]
    ring

end Formalism.L2.AlgTh
