import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GoodPlaces

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Code

/- English proof (translation)
Establish `hfin : Finite (A ⧸ H.subgroupOf A)` using `by choose rep hrep using fun v : Set.range φ => v.2`. Use `Finite.of_surjective (fun v : Set.range φ => (QuotientGroup.mk (rep v) : A ⧸ H.subgroupOf A)) ?_` and prove the remaining obligations. Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H k`.

Use `⟨⟨φ k, k, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show (QuotientGroup.mk (rep ⟨φ k, k, rfl⟩) : A ⧸ H.subgroupOf A) = QuotientGroup.mk k`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Conclude with `hφ _ _ (hrep _)`. Rewrite using `[Subgroup.relIndex]`.

Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_code {G : Type*} [Group G] (H A : Subgroup G) {Q : Type*} [Finite Q] (φ : A → Q)
    (hφ : ∀ k k' : A, φ k = φ k' → ((k⁻¹ * k' : A) : G) ∈ H) : H.relIndex A ≠ 0 := by
  classical
  have hfin : Finite (A ⧸ H.subgroupOf A) := by
    choose rep hrep using fun v : Set.range φ => v.2
    refine Finite.of_surjective (fun v : Set.range φ => (QuotientGroup.mk (rep v) : A ⧸ H.subgroupOf A)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      refine ⟨⟨φ k, k, rfl⟩, ?_⟩
      show (QuotientGroup.mk (rep ⟨φ k, k, rfl⟩) : A ⧸ H.subgroupOf A) = QuotientGroup.mk k
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact hφ _ _ (hrep _)
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

end Code

section Fin

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

/- English proof (translation)
Take `⟨-, -, -, hO, -, hsp⟩` from `hA`. Use `revert hx`. Use `show x ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R → _`. Break down `hM : (M p).split with _ | g` into its components or cases. Introduce `hx`.

Establish `: x ∈ (M p).L.O` using `hx`. Rewrite `this` using `[hO]`. Then use the resulting hypothesis. Break down `hR : (D.s.atP p).split with _ | sg` into its components or cases. Simplify using `[hM, hR] at hsp`. Establish `hsp' : g.e = sg.e ∧ g.q = sg.q` using `by simpa [hM, hR] using hsp`.

Introduce `hx`. Rewrite `hx` using `[Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split]`. Rewrite using `[Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1]`. Conclude with `⟨hx.1, hx.2.1⟩`.
-/
theorem R_sub_O {p : PlF D} (hA : Agree δ M p) {x : (D.s.atP p).Ep} (hx : x ∈ (M p).R) : x ∈ (D.s.atP p).O := by
  obtain ⟨-, -, -, hO, -, hsp⟩ := hA
  revert hx
  show x ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R → _
  rcases hM : (M p).split with _ | g
  · intro hx
    have : x ∈ (M p).L.O := hx
    rwa [hO] at this
  · rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      intro hx
      rw [Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split] at hx
      rw [Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1]
      exact ⟨hx.1, hx.2.1⟩

def dO {p : PlF D} (c : (D.s.atP p).Fp) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).O :=
  ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c, alg_mem_O hc⟩

/- English proof (translation)
Take `⟨hOK, -, -, hO, -, -⟩` from `hA`. Use `hOK.loc` as an intermediate fact. Use `hOK.char0` as an intermediate fact. Use `Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK` as an intermediate fact. Take `⟨hOo, hOc, -⟩` from `Formalism.MainNotions.LocalModelPeriodLattices.O_top (M p).L`.

Rewrite `hOo`, `hOc` using `[hO]`. Establish `: CompactSpace (D.s.atP p).O` using `isCompact_iff_compactSpace.1 hOc`. Establish `hc' : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hc0, map_one]`. Establish `hopen : IsOpen (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O)`.

Establish `h1 : (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) = (fun y : (D.s.atP p).O => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep)) ⁻¹' ((D.s.atP p).O : Set (D.s.atP p).Ep)`. Use extensionality with `y`. Simplify using `only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_preimage]`. Rewrite using `[Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, rfl⟩ show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * ((z : (D.s.atP p).Ep) * algebraMap _ _ c) ∈ (D.s.atP p).O`. Rewrite using `[mul_comm (z : (D.s.atP p).Ep), ← mul_assoc, hc', one_mul]`. Conclude with `z.2`. Introduce `hy`. Use `⟨⟨_, hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Use `show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep) * algebraMap _ _ c = y`. Rewrite using `[mul_comm, ← mul_assoc, mul_comm (algebraMap _ _ c), hc', one_mul]`. Rewrite using `[h1]`. Conclude with `hOo.preimage (by fun_prop)`. Conclude with `AddSubgroup.quotient_finite_of_isOpen _ hopen`.
-/
theorem finite_quot {p : PlF D} (hA : Agree δ M p) (c : (D.s.atP p).Fp) (hc0 : c ≠ 0) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    Finite ((D.s.atP p).O ⧸ (Ideal.span {dO c hc}).toAddSubgroup) := by
  obtain ⟨hOK, -, -, hO, -, -⟩ := hA
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  obtain ⟨hOo, hOc, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top (M p).L
  rw [hO] at hOo hOc
  have : CompactSpace (D.s.atP p).O := isCompact_iff_compactSpace.1 hOc
  have hc' : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  have hopen : IsOpen (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) := by
    have h1 : (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) =
        (fun y : (D.s.atP p).O => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep)) ⁻¹'
          ((D.s.atP p).O : Set (D.s.atP p).Ep) := by
      ext y
      simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_preimage]
      rw [Ideal.mem_span_singleton']
      constructor
      · rintro ⟨z, rfl⟩
        show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * ((z : (D.s.atP p).Ep) * algebraMap _ _ c) ∈ (D.s.atP p).O
        rw [mul_comm (z : (D.s.atP p).Ep), ← mul_assoc, hc', one_mul]
        exact z.2
      · intro hy
        refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
        show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep) * algebraMap _ _ c = y
        rw [mul_comm, ← mul_assoc, mul_comm (algebraMap _ _ c), hc', one_mul]
    rw [h1]
    exact hOo.preimage (by fun_prop)
  exact AddSubgroup.quotient_finite_of_isOpen _ hopen

/- English proof (translation)
Rewrite `h` using `[QuotientAddGroup.eq]`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 h`. Use `mem_latS.2 ⟨z, z.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hz` as an intermediate fact. Simplify using `only [Subring.coe_mul, Subring.coe_add, Subring.coe_neg] at this`.

Rewrite using `[show (y : (D.s.atP p).Ep) - x = -x + y by ring, ← this]`. Use `show (z : (D.s.atP p).Ep) * algebraMap _ _ c = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quot_eq {p : PlF D} {c : (D.s.atP p).Fp} {hc : c ∈ 𝒪[(D.s.atP p).Fp]} {x y : (D.s.atP p).O}
    (h : (QuotientAddGroup.mk x : (D.s.atP p).O ⧸ (Ideal.span {dO c hc}).toAddSubgroup) = QuotientAddGroup.mk y) :
    (y : (D.s.atP p).Ep) - x ∈ latS (D.s.atP p) c := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  refine mem_latS.2 ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_neg] at this
  rw [show (y : (D.s.atP p).Ep) - x = -x + y by ring, ← this]
  show (z : (D.s.atP p).Ep) * algebraMap _ _ c = _
  ring

/- English proof (translation)
The claim follows from `entIn_mul (J1 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => O_mul_latS hx hy) (fun i j => hB i j) hX`.
-/
theorem entIn_int_mul {p : PlF D} {c : (D.s.atP p).Fp} {B X : ProdE.MP p} (hB : ∀ i j, B i j ∈ (D.s.atP p).O)
    (hX : EntIn (latS (D.s.atP p) c) X) : EntIn (latS (D.s.atP p) c) (B * X) :=
  entIn_mul (J1 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => O_mul_latS hx hy) (fun i j => hB i j) hX

/- English proof (translation)
The claim follows from `entIn_mul (J2 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => by rw [mul_comm]; exact O_mul_latS hy hx) hX (fun i j => hB i j)`.
-/
theorem entIn_mul_int {p : PlF D} {c : (D.s.atP p).Fp} {B X : ProdE.MP p} (hB : ∀ i j, B i j ∈ (D.s.atP p).O)
    (hX : EntIn (latS (D.s.atP p) c) X) : EntIn (latS (D.s.atP p) c) (X * B) :=
  entIn_mul (J2 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => by rw [mul_comm]; exact O_mul_latS hy hx) hX
    (fun i j => hB i j)

end Fin

end Formalism.L2.SG.Pf.ProdEApprox
