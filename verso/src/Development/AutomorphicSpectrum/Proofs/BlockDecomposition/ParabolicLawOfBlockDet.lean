import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisPar

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]

/- English proof (translation)
Apply the tactic sequence `first | fun_prop | exact continuous_subtype_val | exact continuous_induced_dom`.
-/
theorem continuous_circle_coe : Continuous (fun z : Circle => (z : ℂ)) := by
  first | fun_prop | exact continuous_subtype_val | exact continuous_induced_dom

/- English proof (translation)
Use `eq_top_iff.2 fun g _ r hr => ?_` and prove the remaining obligations. Conclude with `absurd (Set.mem_univ r) hr`.
-/
theorem stab_univ_eq_top {κ : Type} [Fintype κ] [DecidableEq κ] : stab R (Set.univ : Set κ) = ⊤ := by
  refine eq_top_iff.2 fun g _ r hr => ?_
  exact absurd (Set.mem_univ r) hr

/- English proof (translation)
Introduce `p _ q _` and use `h.mul p trivial q trivial norm := fun p _ => h.norm p trivial rat := fun γ hγ _ => h.rat γ hγ trivial cont := (h.cont.mono (Set.subset_univ _ |>.trans (by simp)))`.
-/
theorem isCh_of_top {G : Type} [Group G] [TopologicalSpace G] {Γ P : Subgroup G} {c : G → ℂ} (h : IsCh Γ ⊤ c) : IsCh Γ P c where
  mul := fun p _ q _ => h.mul p trivial q trivial
  norm := fun p _ => h.norm p trivial
  rat := fun γ hγ _ => h.rat γ hγ trivial
  cont := (h.cont.mono (Set.subset_univ _ |>.trans (by simp)))

/- English proof (translation)
Take `⟨-, hm, hcont, hr, -, hd⟩` from `hB E R A hA κ Set.univ`. Establish `htop : ∀ g : GL κ R, g ∈ stab R (Set.univ : Set κ)` using `fun g => by`. Rewrite using `[stab_univ_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Establish `hc : ∀ g : GL κ R, A.cGL κ g = A.χ (bdet Set.univ g)` using `fun g => by`.

Rewrite using `[hd]`. Both sides reduce to the same expression. Use `⟨fun p _ q _ => ?_, fun p _ => ?_, fun γ hγ _ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, hc, hc, hm p (htop p) q (htop q), map_mul, Circle.coe_mul]`. Rewrite using `[hc]`.

Conclude with `Circle.norm_coe _`. Take `⟨x, hx⟩` from `hr γ (htop γ) hγ`. Rewrite using `[hc, hx, hA.χi, Circle.coe_one]`. Establish `hcon : Continuous (bdet (R` using `R) (Set.univ : Set κ)) := by`. Rewrite using `[← continuousOn_univ]`.

Use `hcont.mono fun g _ => htop g` and prove the remaining obligations. Establish `: A.cGL κ = fun g => ((A.χ (bdet Set.univ g) : Circle) : ℂ)` using `funext hc`. Rewrite using `[this]`. Conclude with `(continuous_circle_coe.comp (hA.χcont.comp hcon)).continuousOn`.
-/
theorem isCh_cGL (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (κ : Type) [Fintype κ] [DecidableEq κ] :
    IsCh (A.ratGL κ) ⊤ (A.cGL κ) := by
  obtain ⟨-, hm, hcont, hr, -, hd⟩ := hB E R A hA κ Set.univ
  have htop : ∀ g : GL κ R, g ∈ stab R (Set.univ : Set κ) := fun g => by
    rw [stab_univ_eq_top]; trivial
  have hc : ∀ g : GL κ R, A.cGL κ g = A.χ (bdet Set.univ g) := fun g => by
    rw [hd]; rfl
  refine ⟨fun p _ q _ => ?_, fun p _ => ?_, fun γ hγ _ => ?_, ?_⟩
  · rw [hc, hc, hc, hm p (htop p) q (htop q), map_mul, Circle.coe_mul]
  · rw [hc]; exact Circle.norm_coe _
  · obtain ⟨x, hx⟩ := hr γ (htop γ) hγ
    rw [hc, hx, hA.χi, Circle.coe_one]
  · have hcon : Continuous (bdet (R := R) (Set.univ : Set κ)) := by
      rw [← continuousOn_univ]
      refine hcont.mono fun g _ => htop g
    have : A.cGL κ = fun g => ((A.χ (bdet Set.univ g) : Circle) : ℂ) := funext hc
    rw [this]
    exact (continuous_circle_coe.comp (hA.χcont.comp hcon)).continuousOn

/- English proof (translation)
Take `⟨hc, hm, hcont, hr, hk, -⟩` from `hB E R A hA.toGoodL κ t`. Use `haveI : T2Space (GL κ R) := (hT E R A hA κ 1).1`. Use `hE (GL κ R) (A.ratGL κ) (A.kGL κ) (stab R t) (fun p => A.lg (bdet t p)) (hA.kcpt κ) hc (hA.iwa κ t) ?_ ?_ hk ?_` and prove the remaining obligations. Introduce `p hp q hq`. Simplify using `only [hm p hp q hq, hA.lgmul]`.

Conclude with `hA.lgcont.comp_continuousOn hcont`. Introduce `p hp hg`. Take `⟨x, hx⟩` from `hr p hp hg`. Simplify using `only [hx, hA.lgi x]`.
-/
theorem ext_gl (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (κ : Type) [Fintype κ] [DecidableEq κ]
    (t : Set κ) : IsHt (A.ratGL κ) (A.kGL κ) (stab R t) (A.htGL t) ∧
      ∀ p ∈ stab R t, ∀ k ∈ A.kGL κ, A.htGL t (p * k) = A.lg (bdet t p) := by
  obtain ⟨hc, hm, hcont, hr, hk, -⟩ := hB E R A hA.toGoodL κ t
  haveI : T2Space (GL κ R) := (hT E R A hA κ 1).1
  refine hE (GL κ R) (A.ratGL κ) (A.kGL κ) (stab R t) (fun p => A.lg (bdet t p)) (hA.kcpt κ) hc (hA.iwa κ t) ?_ ?_ hk ?_
  · intro p hp q hq
    simp only [hm p hp q hq, hA.lgmul]
  · exact hA.lgcont.comp_continuousOn hcont
  · intro p hp hg
    obtain ⟨x, hx⟩ := hr p hp hg
    simp only [hx, hA.lgi x]

/- English proof (translation)
The claim follows from `(hB E R A hA (κ ⊕ κ) (Sum.inl '' t)).1.preimage continuous_subtype_val`.
-/
theorem closed_uQ (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (ε : ℤˣ) {κ : Type} [Fintype κ] [DecidableEq κ] (t : Set κ) :
    IsClosed (A.uQ ε t : Set (A.U ε κ)) :=
  (hB E R A hA (κ ⊕ κ) (Sum.inl '' t)).1.preimage continuous_subtype_val

/- English proof (translation)
Take `⟨-, hm, hcont, hr, hk, -⟩` from `hB E R A hA.toGoodL (κ ⊕ κ) (Sum.inl '' t)`. Take `⟨-, -, -, h2, -, -, hK⟩` from `hT E R A hA κ ε`. Use `haveI := h2`. Use `hE (A.U ε κ) (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (fun p => A.lg (bdet (Sum.inl '' t) p.1)) hK (closed_uQ hB A hA.toGoodL ε t) hI ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp q hq`.

Simplify using `only [Subgroup.coe_mul, hm p.1 hp q.1 hq, hA.lgmul]`. Conclude with `hA.lgcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx)`. Conclude with `fun p hp hpk => hk p.1 hp hpk`. Introduce `p hp hg`. Take `⟨x, hx⟩` from `hr p.1 hp hg`.

Simplify using `only [hx, hA.lgi x]`.
-/
theorem ext_u (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (ε : ℤˣ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (t : Set κ) (hI : Iwa (A.uQ ε t) (A.uK ε κ)) :
    IsHt (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (A.uH ε t) ∧
      ∀ p ∈ A.uQ ε t, ∀ k ∈ A.uK ε κ, A.uH ε t (p * k) = A.lg (bdet (Sum.inl '' t) p.1) := by
  obtain ⟨-, hm, hcont, hr, hk, -⟩ := hB E R A hA.toGoodL (κ ⊕ κ) (Sum.inl '' t)
  obtain ⟨-, -, -, h2, -, -, hK⟩ := hT E R A hA κ ε
  haveI := h2
  refine hE (A.U ε κ) (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (fun p => A.lg (bdet (Sum.inl '' t) p.1)) hK
    (closed_uQ hB A hA.toGoodL ε t) hI ?_ ?_ ?_ ?_
  · intro p hp q hq
    simp only [Subgroup.coe_mul, hm p.1 hp q.1 hq, hA.lgmul]
  · exact hA.lgcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx)
  · exact fun p hp hpk => hk p.1 hp hpk
  · intro p hp hg
    obtain ⟨x, hx⟩ := hr p.1 hp hg
    simp only [hx, hA.lgi x]

/- English proof (translation)
Take `⟨-, hm, hcont, hr, -, -⟩` from `hB E R A hA (κ ⊕ κ) (Sum.inl '' (Set.univ : Set κ))`. Use `⟨fun p hp q hq => ?_, fun p _ => Circle.norm_coe _, fun γ hγ hp => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Ad.uC, Subgroup.coe_mul, hm p.1 hp q.1 hq, map_mul, Circle.coe_mul]`. Take `⟨x, hx⟩` from `hr γ.1 hp hγ`. Simplify using `only [Ad.uC, hx, hA.χi, Circle.coe_one]`.

Conclude with `continuous_circle_coe.comp_continuousOn (hA.χcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx))`.
-/
theorem isCh_uC (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (ε : ℤˣ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    IsCh (A.uΓ ε κ) (A.uQ ε (Set.univ : Set κ)) (A.uC ε κ) := by
  obtain ⟨-, hm, hcont, hr, -, -⟩ := hB E R A hA (κ ⊕ κ) (Sum.inl '' (Set.univ : Set κ))
  refine ⟨fun p hp q hq => ?_, fun p _ => Circle.norm_coe _, fun γ hγ hp => ?_, ?_⟩
  · simp only [Ad.uC, Subgroup.coe_mul, hm p.1 hp q.1 hq, map_mul, Circle.coe_mul]
  · obtain ⟨x, hx⟩ := hr γ.1 hp hγ
    simp only [Ad.uC, hx, hA.χi, Circle.coe_one]
  · exact continuous_circle_coe.comp_continuousOn
      (hA.χcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx))

/- English proof (translation)
Introduce `hB hE hT E R _ _ _ _ _ _ _ A hA ι _ _ ε s`. Take `⟨hc, -⟩` from `hB E R A hA.toGoodL ι s`. Establish `hch` using `isCh_cGL hB A hA.toGoodL ι`. Use `⟨⟨⟨hc, hA.iwa ι s, ?_⟩, ⟨hc, hA.iwa ι s, isCh_of_top hch⟩, hch, (ext_gl hB hE hT A hA ι s).1, stab_univ_eq_top⟩, ?_⟩` and prove the remaining obligations. Use `⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl, continuousOn_const⟩` and prove the remaining obligations.

Introduce `hI`. Establish `hI' : Iwa (A.uQ ε s) (A.uK ε ι)` using `fun g => by`. Take `⟨p, hp, k, hk, e⟩` from `hI g`. Conclude with `⟨p, hp.1, k, hk, e⟩`. Establish `hu` using `ext_u hB hE hT A hA ε s hI'`.

Establish `hC` using `isCh_uC hB A hA.toGoodL (ε := ε) (κ := ι)`. Use `⟨⟨(closed_uQ hB A hA.toGoodL ε s).inter (closed_uQ hB A hA.toGoodL ε Set.univ), hI, ?_⟩, hu.1, fun g => ?_⟩` and prove the remaining obligations. Conclude with `⟨fun p hp q hq => hC.mul p hp.2 q hq.2, fun p hp => hC.norm p hp.2, fun γ hγ hp => hC.rat γ hγ hp.2, hC.cont.mono fun _ h => h.2⟩`. Take `⟨p, hp, k, hk, rfl⟩` from `hI' g`. Rewrite using `[hu.2 p hp k hk]`.

Conclude with `((ext_gl hB hE hT A hA (ι ⊕ ι) (Sum.inl '' s)).2 p.1 hp k.1 hk).symm`.
-/
theorem parLaw : BdetLaw → ExtLaw → GrpTop → ParLaw := by
  intro hB hE hT E R _ _ _ _ _ _ _ A hA ι _ _ ε s
  obtain ⟨hc, -⟩ := hB E R A hA.toGoodL ι s
  have hch := isCh_cGL hB A hA.toGoodL ι
  refine ⟨⟨⟨hc, hA.iwa ι s, ?_⟩, ⟨hc, hA.iwa ι s, isCh_of_top hch⟩, hch, (ext_gl hB hE hT A hA ι s).1, stab_univ_eq_top⟩, ?_⟩
  · refine ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl, continuousOn_const⟩
  intro hI
  have hI' : Iwa (A.uQ ε s) (A.uK ε ι) := fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := hI g
    exact ⟨p, hp.1, k, hk, e⟩
  have hu := ext_u hB hE hT A hA ε s hI'
  have hC := isCh_uC hB A hA.toGoodL (ε := ε) (κ := ι)
  refine ⟨⟨(closed_uQ hB A hA.toGoodL ε s).inter (closed_uQ hB A hA.toGoodL ε Set.univ), hI, ?_⟩, hu.1, fun g => ?_⟩
  · exact ⟨fun p hp q hq => hC.mul p hp.2 q hq.2, fun p hp => hC.norm p hp.2, fun γ hγ hp => hC.rat γ hγ hp.2,
      hC.cont.mono fun _ h => h.2⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := hI' g
    rw [hu.2 p hp k hk]
    exact ((ext_gl hB hE hT A hA (ι ⊕ ι) (Sum.inl '' s)).2 p.1 hp k.1 hk).symm

end GlobalTheory.CompanionTheory.RgEisPar
