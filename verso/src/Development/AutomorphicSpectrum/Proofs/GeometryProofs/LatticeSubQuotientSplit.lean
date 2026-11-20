import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameOpenNeighbourhoodStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeClosureStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFractionStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SatSub

open Submodule Module

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Establish `h1 : Module.Projective R A` using `Module.Projective.of_split A.subtype (Submodule.linearProjOfIsCompl A B h) (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)`. Establish `h2 : Module.Finite R A` using `Module.Finite.of_surjective (Submodule.linearProjOfIsCompl A B h) (Submodule.linearProjOfIsCompl_surjective h)`. Establish `h3 : Module.FinitePresentation R A` using `Module.finitePresentation_of_projective R A`. Establish `h4 : Module.Free R A` using `Module.free_of_flat_of_isLocalRing`. Conclude with `⟨_, ⟨Module.finBasis R A⟩⟩`.
-/
theorem exists_basis_of_isCompl (R : Type) [CommRing R] [IsLocalRing R] {M : Type} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (A B : Submodule R M) (h : IsCompl A B) :
    ∃ k : ℕ, Nonempty (Module.Basis (Fin k) R A) := by
  have h1 : Module.Projective R A :=
    Module.Projective.of_split A.subtype (Submodule.linearProjOfIsCompl A B h)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)
  have h2 : Module.Finite R A :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl A B h) (Submodule.linearProjOfIsCompl_surjective h)
  have h3 : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  have h4 : Module.Free R A := Module.free_of_flat_of_isLocalRing
  exact ⟨_, ⟨Module.finBasis R A⟩⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `(mem_span_range_iff_exists_fun Ω).1 hy`. Establish `h0 : ∑ i, a i • V.mkQ (e i) = 0`. Establish `h` using `(Submodule.Quotient.mk_eq_zero V).2 hyV`. Rewrite `h` using `[← Submodule.mkQ_apply, map_sum]`. Simplify using `using h`.

Establish `ha` using `Fintype.linearIndependent_iff.1 hc a h0`. Simplify using `[ha]`.
-/
theorem eq_zero_of_mem {V : Submodule Ω E} {s : ℕ} {e : Fin s → E}
    (hc : LinearIndependent Ω fun i => V.mkQ (e i)) {y : E} (hy : y ∈ span Ω (Set.range e)) (hyV : y ∈ V) :
    y = 0 := by
  obtain ⟨a, rfl⟩ := (mem_span_range_iff_exists_fun Ω).1 hy
  have h0 : ∑ i, a i • V.mkQ (e i) = 0 := by
    have h := (Submodule.Quotient.mk_eq_zero V).2 hyV
    rw [← Submodule.mkQ_apply, map_sum] at h
    simpa using h
  have ha := Fintype.linearIndependent_iff.1 hc a h0
  simp [ha]

/- English proof (translation)
Establish `hnV : span R (Set.range n) ≤ V.restrictScalars R` using `span_le.2 (by rintro _ ⟨j, rfl⟩; exact hn j)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨hx, hxV⟩`. Take `⟨y, hy, z, hz, rfl⟩` from `mem_sup.1 hx`. Establish `hy0 : y = 0` using `eq_zero_of_mem hc (span_le_restrictScalars R Ω _ hy) (by`.

Establish `h` using `V.sub_mem hxV (hnV hz)`. Simplify using `using h)`. Simplify `hz` using `[hy0]`. Conclude with `le_inf le_sup_right hnV`.
-/
theorem sup_inf_eq (R : Subring Ω) {V : Submodule Ω E} {s k : ℕ} {e : Fin s → E} {n : Fin k → E}
    (hc : LinearIndependent Ω fun i => V.mkQ (e i)) (hn : ∀ j, n j ∈ V) :
    (span R (Set.range e) ⊔ span R (Set.range n)) ⊓ V.restrictScalars R = span R (Set.range n) := by
  have hnV : span R (Set.range n) ≤ V.restrictScalars R := span_le.2 (by rintro _ ⟨j, rfl⟩; exact hn j)
  apply le_antisymm
  · rintro x ⟨hx, hxV⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hx
    have hy0 : y = 0 := eq_zero_of_mem hc (span_le_restrictScalars R Ω _ hy) (by
      have h := V.sub_mem hxV (hnV hz)
      simpa using h)
    simpa [hy0] using hz
  · exact le_inf le_sup_right hnV

def cat {s k : ℕ} (e : Fin s → E) (n : Fin k → E) : Fin (s + k) → E := Sum.elim e n ∘ finSumFinEquiv.symm

/- English proof (translation)
Rewrite using `[cat, EquivLike.range_comp, Set.Sum.elim_range]`.
-/
theorem range_cat {s k : ℕ} (e : Fin s → E) (n : Fin k → E) : Set.range (cat e n) = Set.range e ∪ Set.range n := by
  rw [cat, EquivLike.range_comp, Set.Sum.elim_range]

/- English proof (translation)
Rewrite using `[range_cat, span_union]`.
-/
theorem span_cat (R : Subring Ω) {s k : ℕ} (e : Fin s → E) (n : Fin k → E) :
    span R (Set.range (cat e n)) = span R (Set.range e) ⊔ span R (Set.range n) := by
  rw [range_cat, span_union]

/- English proof (translation)
Establish `hinj : Function.Injective fun r : R => r • (1 : Ω)` using `fun x y h => by`. Simplify `h` using `[Subring.smul_def]`. Establish `hlift : ∀ i, ∃ x ∈ P, V.mkQ x = c i` using `fun i => by`. Establish `h : c i ∈ P.map (V.mkQ.restrictScalars R)`. Rewrite using `[hPc]`.

Conclude with `subset_span ⟨i, rfl⟩`. Take `⟨x, hx, e⟩` from `h`. Conclude with `⟨x, hx, e⟩`. Use `choose e heP hec using hlift`. Establish `hc' : LinearIndependent Ω fun i => V.mkQ (e i)` using `by simpa only [hec] using hc`.

Use `set Q := span R (Set.range e) with hQ`. Use `set N := P ⊓ V.restrictScalars R with hN`. Establish `hQP : Q ≤ P` using `span_le.2 (by rintro _ ⟨i, rfl⟩; exact heP i)`. Establish `hdec : ∀ x ∈ P, ∃ y ∈ Q, ∃ z ∈ N, y + z = x` using `fun x hx => by`. Establish `h : V.mkQ x ∈ span R (Set.range c)`.

Rewrite using `[← hPc]`. Conclude with `⟨x, hx, rfl⟩`. Take `⟨a, ha⟩` from `(mem_span_range_iff_exists_fun R).1 h`. Establish `hy : ∑ i, a i • e i ∈ Q` using `sum_mem fun i _ => Q.smul_mem _ (subset_span ⟨i, rfl⟩)`. Use `⟨_, hy, x - ∑ i, a i • e i, ⟨P.sub_mem hx (hQP hy), ?_⟩, by abel⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `x - ∑ i, a i • e i ∈ V`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← ha, map_sum]`. Simplify using `[hec, Subring.smul_def]`. Establish `hdisj : ∀ x, x ∈ Q → x ∈ N → x = 0` using `fun x hx hxN => eq_zero_of_mem hc' (span_le_restrictScalars R Ω _ hx) hxN.2`. Establish `hbR : LinearIndependent R b` using `hb.restrict_scalars hinj`.

Establish `hfree : Module.Free R P`. Substitute `hP` using the available equality. Conclude with `Module.Free.of_basis (Module.Basis.span hbR)`. Establish `hfin : Module.Finite R P`. Substitute `hP` using the available equality.

Conclude with `Module.Finite.span_of_finite R (Set.finite_range b)`. Establish `hcompl : IsCompl (N.comap P.subtype) (Q.comap P.subtype)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `x h1 h2`.

Conclude with `Subtype.ext (hdisj _ h2 h1)`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `x _`. Take `⟨y, hy, z, hz, e⟩` from `hdec x x.2`. Use `mem_sup.2 ⟨⟨z, hz.1⟩, hz, ⟨y, hQP hy⟩, hy, Subtype.ext ?_⟩` and prove the remaining obligations.

Simplify `e` using `[add_comm]`. Take `⟨k, ⟨β⟩⟩` from `exists_basis_of_isCompl R _ _ hcompl`. Set `φ : (N.comap P.subtype) →ₗ[R] E` to `P.subtype ∘ₗ (N.comap P.subtype).subtype`. Establish `hφ : Function.Injective φ` using `fun x y h => Subtype.ext (Subtype.ext h)`. Establish `hφr : LinearMap.range φ = N`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`. Introduce `h`.

Conclude with `⟨⟨⟨x, h.1⟩, h⟩, rfl⟩`. Set `n : Fin k → E` to `fun j => φ (β j)`. Establish `hnN : span R (Set.range n) = N`. Establish `h : Set.range n = φ '' Set.range β`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[h, ← Submodule.map_span, β.span_eq, Submodule.map_top, hφr]`. Establish `hnR : LinearIndependent R n` using `β.linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφ)`. Establish `hnV : ∀ j, n j ∈ V` using `fun j => by`. Establish `h : n j ∈ N` using `by rw [← hφr]; exact ⟨_, rfl⟩`.

Conclude with `h.2`. Establish `hPsup : P = Q ⊔ span R (Set.range n)`. Rewrite using `[hnN]`. Use `le_antisymm (fun x hx => ?_) (sup_le hQP inf_le_left)` and prove the remaining obligations. Take `⟨y, hy, z, hz, rfl⟩` from `hdec x hx`.

Conclude with `add_mem (mem_sup_left hy) (mem_sup_right hz)`. Establish `heR : LinearIndependent R e`. Establish `h : LinearIndependent R ((V.mkQ.restrictScalars R) ∘ e)` using `hc'.restrict_scalars hinj`. Conclude with `h.of_comp _`. Establish `hdisj' : Disjoint (span R (Set.range e)) (span R (Set.range n))`.

Rewrite using `[hnN, Submodule.disjoint_def]`. Conclude with `hdisj`. Establish `hsumR : LinearIndependent R (Sum.elim e n)` using `heR.sum_type hnR hdisj'`. Establish `hcatR : LinearIndependent R (cat e n)` using `hsumR.comp _ (Equiv.injective _)`. Establish `hspan : span R (Set.range (cat e n)) = P` using `by rw [span_cat, hPsup, hnN]`.

Establish `hcard : g = s + k`. Establish `h1` using `finrank_span_eq_card hbR`. Establish `h2` using `finrank_span_eq_card hcatR`. Rewrite `h2` using `[hspan]`. Rewrite `h1` using `[← hP]`.

Simplify using `using h1.symm.trans h2`. Establish `hPW : ∀ {x}, x ∈ P → x ∈ W` using `fun {x} hx => by`. Rewrite `hx` using `[hP]`. Rewrite using `[← hbW]`. Conclude with `span_le_restrictScalars R Ω _ hx`.

Establish `hW : span Ω (Set.range (cat e n)) = W`. Apply `le_antisymm` to reduce the goal to its premises. Use `span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Use `hPW ?_` and prove the remaining obligations.

Rewrite using `[← hspan]`. Conclude with `subset_span ⟨i, rfl⟩`. Rewrite using `[← hbW]`. Use `span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Establish `h : b i ∈ span R (Set.range (cat e n))`. Rewrite using `[hspan, hP]`. Conclude with `subset_span ⟨i, rfl⟩`. Conclude with `span_le_restrictScalars R Ω _ h`. Establish `hcatΩ : LinearIndependent Ω (cat e n)`.

Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Set.finrank, hW, ← hbW, finrank_span_eq_card hb]`. Simplify using `[hcard]`. Establish `hsumΩ : LinearIndependent Ω (Sum.elim e n)`. Establish `h` using `hcatΩ.comp _ (finSumFinEquiv (m := s) (n := k)).injective`. Simplify `h` using `[cat, Function.comp_def]`.

Use `⟨k, e, n, hcatΩ, hPsup, hc', hnV, le_antisymm (span_le.2 ?_) fun v hv => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hnV j`. Establish `hvW` using `hVW hv`. Rewrite `hvW` using `[← hW, range_cat, span_union]`.

Take `⟨y, hy, z, hz, rfl⟩` from `mem_sup.1 hvW`. Establish `hzV : z ∈ V` using `(span_le.2 (by rintro _ ⟨j, rfl⟩; exact hnV j) : span Ω (Set.range n) ≤ V) hz`. Establish `hy0 : y = 0` using `eq_zero_of_mem hc' hy (by`. Establish `h` using `V.sub_mem hv hzV`. Simplify using `using h)`.

Simplify `hz` using `[hy0]`.
-/
theorem exists_frame (R : Subring Ω) [IsLocalRing R] {V W : Submodule Ω E} (hVW : V ≤ W) (P : Submodule R E)
    {g s : ℕ} (b : Fin g → E) (hb : LinearIndependent Ω b) (hbW : span Ω (Set.range b) = W)
    (hP : P = span R (Set.range b)) (c : Fin s → E ⧸ V) (hc : LinearIndependent Ω c)
    (hPc : P.map (V.mkQ.restrictScalars R) = span R (Set.range c)) :
    ∃ (k : ℕ) (e : Fin s → E) (n : Fin k → E), LinearIndependent Ω (cat e n) ∧
      P = span R (Set.range e) ⊔ span R (Set.range n) ∧ (LinearIndependent Ω fun i => V.mkQ (e i)) ∧
      (∀ j, n j ∈ V) ∧ span Ω (Set.range n) = V := by
  have hinj : Function.Injective fun r : R => r • (1 : Ω) := fun x y h => by
    simpa [Subring.smul_def] using h

  have hlift : ∀ i, ∃ x ∈ P, V.mkQ x = c i := fun i => by
    have h : c i ∈ P.map (V.mkQ.restrictScalars R) := by
      rw [hPc]; exact subset_span ⟨i, rfl⟩
    obtain ⟨x, hx, e⟩ := h
    exact ⟨x, hx, e⟩
  choose e heP hec using hlift
  have hc' : LinearIndependent Ω fun i => V.mkQ (e i) := by simpa only [hec] using hc
  set Q := span R (Set.range e) with hQ
  set N := P ⊓ V.restrictScalars R with hN
  have hQP : Q ≤ P := span_le.2 (by rintro _ ⟨i, rfl⟩; exact heP i)
  have hdec : ∀ x ∈ P, ∃ y ∈ Q, ∃ z ∈ N, y + z = x := fun x hx => by
    have h : V.mkQ x ∈ span R (Set.range c) := by
      rw [← hPc]; exact ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := (mem_span_range_iff_exists_fun R).1 h
    have hy : ∑ i, a i • e i ∈ Q := sum_mem fun i _ => Q.smul_mem _ (subset_span ⟨i, rfl⟩)
    refine ⟨_, hy, x - ∑ i, a i • e i, ⟨P.sub_mem hx (hQP hy), ?_⟩, by abel⟩
    change x - ∑ i, a i • e i ∈ V
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← ha, map_sum]
    simp [hec, Subring.smul_def]
  have hdisj : ∀ x, x ∈ Q → x ∈ N → x = 0 := fun x hx hxN =>
    eq_zero_of_mem hc' (span_le_restrictScalars R Ω _ hx) hxN.2

  have hbR : LinearIndependent R b := hb.restrict_scalars hinj
  have hfree : Module.Free R P := by
    subst hP; exact Module.Free.of_basis (Module.Basis.span hbR)
  have hfin : Module.Finite R P := by
    subst hP; exact Module.Finite.span_of_finite R (Set.finite_range b)
  have hcompl : IsCompl (N.comap P.subtype) (Q.comap P.subtype) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x h1 h2
      exact Subtype.ext (hdisj _ h2 h1)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      obtain ⟨y, hy, z, hz, e⟩ := hdec x x.2
      refine mem_sup.2 ⟨⟨z, hz.1⟩, hz, ⟨y, hQP hy⟩, hy, Subtype.ext ?_⟩
      simpa [add_comm] using e
  obtain ⟨k, ⟨β⟩⟩ := exists_basis_of_isCompl R _ _ hcompl
  let φ : (N.comap P.subtype) →ₗ[R] E := P.subtype ∘ₗ (N.comap P.subtype).subtype
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (Subtype.ext h)
  have hφr : LinearMap.range φ = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro h; exact ⟨⟨⟨x, h.1⟩, h⟩, rfl⟩
  let n : Fin k → E := fun j => φ (β j)
  have hnN : span R (Set.range n) = N := by
    have h : Set.range n = φ '' Set.range β := by
      rw [← Set.range_comp]; rfl
    rw [h, ← Submodule.map_span, β.span_eq, Submodule.map_top, hφr]
  have hnR : LinearIndependent R n := β.linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have hnV : ∀ j, n j ∈ V := fun j => by
    have h : n j ∈ N := by rw [← hφr]; exact ⟨_, rfl⟩
    exact h.2
  have hPsup : P = Q ⊔ span R (Set.range n) := by
    rw [hnN]
    refine le_antisymm (fun x hx => ?_) (sup_le hQP inf_le_left)
    obtain ⟨y, hy, z, hz, rfl⟩ := hdec x hx
    exact add_mem (mem_sup_left hy) (mem_sup_right hz)

  have heR : LinearIndependent R e := by
    have h : LinearIndependent R ((V.mkQ.restrictScalars R) ∘ e) := hc'.restrict_scalars hinj
    exact h.of_comp _
  have hdisj' : Disjoint (span R (Set.range e)) (span R (Set.range n)) := by
    rw [hnN, Submodule.disjoint_def]
    exact hdisj
  have hsumR : LinearIndependent R (Sum.elim e n) := heR.sum_type hnR hdisj'
  have hcatR : LinearIndependent R (cat e n) := hsumR.comp _ (Equiv.injective _)
  have hspan : span R (Set.range (cat e n)) = P := by rw [span_cat, hPsup, hnN]
  have hcard : g = s + k := by
    have h1 := finrank_span_eq_card hbR
    have h2 := finrank_span_eq_card hcatR
    rw [hspan] at h2
    rw [← hP] at h1
    simpa using h1.symm.trans h2

  have hPW : ∀ {x}, x ∈ P → x ∈ W := fun {x} hx => by
    rw [hP] at hx
    rw [← hbW]
    exact span_le_restrictScalars R Ω _ hx
  have hW : span Ω (Set.range (cat e n)) = W := by
    apply le_antisymm
    · refine span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      refine hPW ?_
      rw [← hspan]
      exact subset_span ⟨i, rfl⟩
    · rw [← hbW]
      refine span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have h : b i ∈ span R (Set.range (cat e n)) := by
        rw [hspan, hP]; exact subset_span ⟨i, rfl⟩
      exact span_le_restrictScalars R Ω _ h
  have hcatΩ : LinearIndependent Ω (cat e n) := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hW, ← hbW, finrank_span_eq_card hb]
    simp [hcard]
  have hsumΩ : LinearIndependent Ω (Sum.elim e n) := by
    have h := hcatΩ.comp _ (finSumFinEquiv (m := s) (n := k)).injective
    simpa [cat, Function.comp_def] using h
  refine ⟨k, e, n, hcatΩ, hPsup, hc', hnV, le_antisymm (span_le.2 ?_) fun v hv => ?_⟩
  · rintro _ ⟨j, rfl⟩; exact hnV j
  · have hvW := hVW hv
    rw [← hW, range_cat, span_union] at hvW
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hvW
    have hzV : z ∈ V := (span_le.2 (by rintro _ ⟨j, rfl⟩; exact hnV j) : span Ω (Set.range n) ≤ V) hz
    have hy0 : y = 0 := eq_zero_of_mem hc' hy (by
      have h := V.sub_mem hv hzV
      simpa using h)
    simpa [hy0] using hz

end GlobalTheory.CompanionTheory.Ar.SatSub

namespace GlobalTheory.CompanionTheory.Ar

open Submodule Module SatSub

/- English proof (translation)
Introduce `X Ω _ ξ E _ _ L T g s W V W' hVW hL hM`. Establish `hcoh : L.IsCohOn T` using `(GlobalTheory.T.coherent_lattice_closure X Ω ξ E E L L T).1 g W hL`. Establish `key : ∀ p ∈ T, ∃ (k : ℕ) (e : Fin s → E) (n : Fin k → E), LinearIndependent Ω (cat e n) ∧ L p = span (regAt ξ p) (Set.range e) ⊔ span (regAt ξ p) (Set.range n) ∧ (LinearIndependent Ω fun i => V.mkQ (e i)) ∧ (∀ j, n j ∈ V) ∧ span Ω (Set.range n) = V` using `fun p hp => by`. Use `(GlobalTheory.T.regAt_local_order_fraction X Ω ξ).1 p` as an intermediate fact. Take `⟨U, hU, b, hbW, hb⟩` from `hL p hp`.

Take `⟨U', hU', c, -, hc⟩` from `hM p hp`. Take `⟨hb1, hb2⟩` from `hb p hp hU`. Take `⟨hc1, hc2⟩` from `hc p hp hU'`. Conclude with `exists_frame (regAt ξ p) hVW (L p) b hb1 hbW hb2 c hc1 hc2`. Use `⟨fun p hp => ?_, fun p hp => ?_⟩` and prove the remaining obligations.

Take `⟨k, e, n, hf, hP, hc, hn, hnV⟩` from `key p hp`. Establish `hnI : LinearIndependent Ω n`. Establish `h` using `hf.comp _ ((finSumFinEquiv (m := s) (n := k)).injective.comp Sum.inr_injective)`. Simplify `h` using `[cat, Function.comp_def]`. Establish `hk : k = Module.finrank Ω V`.

Rewrite using `[← hnV, finrank_span_eq_card hnI]`. Simplify using the standard rewrite rules. Substitute `hk` using the available equality. Take `⟨U, hU, h⟩` from `GlobalTheory.T.frame_open_neighbourhood X Ω ξ E L T _ (cat e n) p hcoh hp ⟨hf, by rw [span_cat]; exact hP⟩`. Use `⟨U, hU, n, hnV, fun q hq hqU => ⟨hnI, ?_⟩⟩` and prove the remaining obligations.

Take `⟨-, h2⟩` from `h q hq hqU`. Rewrite `h2` using `[span_cat]`. Express the relevant statement in the definitionally equal form `L q ⊓ V.restrictScalars (regAt ξ q) = _`. Rewrite using `[h2]`. Conclude with `sup_inf_eq (regAt ξ q) hc hn`.

Take `⟨k, e, n, hf, hP, hc, hn, hnV⟩` from `key p hp`. Establish `hint : L.inter V p = span (regAt ξ p) (Set.range n)`. Express the relevant statement in the definitionally equal form `L p ⊓ V.restrictScalars (regAt ξ p) = _`. Rewrite using `[hP]`. Conclude with `sup_inf_eq (regAt ξ p) hc hn`.

Use `⟨span (regAt ξ p) (Set.range e), ?_, by rw [hint, ← hP]⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx hx'`. Establish `hxV : x ∈ V`. Rewrite `hx'` using `[hint]`.

Conclude with `(span_le.2 (by rintro _ ⟨j, rfl⟩; exact hn j) : span Ω (Set.range n) ≤ V) (span_le_restrictScalars (regAt ξ p) Ω _ hx')`. Conclude with `eq_zero_of_mem hc (span_le_restrictScalars (regAt ξ p) Ω _ hx) hxV`.
-/
theorem inter_isVBOn_of_map : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (g s : ℕ) (W V : Submodule Ω E)
    (W' : Submodule Ω (E ⧸ V)), V ≤ W → L.IsVBOn T g W → (L.map V.mkQ).IsVBOn T s W' →
    (L.inter V).IsVBOn T (Module.finrank Ω V) V ∧
      ∀ p ∈ T, ∃ Q : Submodule (regAt ξ p) E, Disjoint Q (L.inter V p) ∧ Q ⊔ L.inter V p = L p := by
  intro X Ω _ ξ E _ _ L T g s W V W' hVW hL hM
  have hcoh : L.IsCohOn T := (GlobalTheory.T.coherent_lattice_closure X Ω ξ E E L L T).1 g W hL
  have key : ∀ p ∈ T, ∃ (k : ℕ) (e : Fin s → E) (n : Fin k → E), LinearIndependent Ω (cat e n) ∧
      L p = span (regAt ξ p) (Set.range e) ⊔ span (regAt ξ p) (Set.range n) ∧
      (LinearIndependent Ω fun i => V.mkQ (e i)) ∧ (∀ j, n j ∈ V) ∧ span Ω (Set.range n) = V := fun p hp => by
    have := (GlobalTheory.T.regAt_local_order_fraction X Ω ξ).1 p
    obtain ⟨U, hU, b, hbW, hb⟩ := hL p hp
    obtain ⟨U', hU', c, -, hc⟩ := hM p hp
    obtain ⟨hb1, hb2⟩ := hb p hp hU
    obtain ⟨hc1, hc2⟩ := hc p hp hU'
    exact exists_frame (regAt ξ p) hVW (L p) b hb1 hbW hb2 c hc1 hc2
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨k, e, n, hf, hP, hc, hn, hnV⟩ := key p hp
    have hnI : LinearIndependent Ω n := by
      have h := hf.comp _ ((finSumFinEquiv (m := s) (n := k)).injective.comp Sum.inr_injective)
      simpa [cat, Function.comp_def] using h
    have hk : k = Module.finrank Ω V := by
      rw [← hnV, finrank_span_eq_card hnI]; simp
    subst hk
    obtain ⟨U, hU, h⟩ := GlobalTheory.T.frame_open_neighbourhood X Ω ξ E L T _ (cat e n) p hcoh hp
      ⟨hf, by rw [span_cat]; exact hP⟩
    refine ⟨U, hU, n, hnV, fun q hq hqU => ⟨hnI, ?_⟩⟩
    obtain ⟨-, h2⟩ := h q hq hqU
    rw [span_cat] at h2
    change L q ⊓ V.restrictScalars (regAt ξ q) = _
    rw [h2]
    exact sup_inf_eq (regAt ξ q) hc hn
  · obtain ⟨k, e, n, hf, hP, hc, hn, hnV⟩ := key p hp
    have hint : L.inter V p = span (regAt ξ p) (Set.range n) := by
      change L p ⊓ V.restrictScalars (regAt ξ p) = _
      rw [hP]
      exact sup_inf_eq (regAt ξ p) hc hn
    refine ⟨span (regAt ξ p) (Set.range e), ?_, by rw [hint, ← hP]⟩
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hxV : x ∈ V := by
      rw [hint] at hx'
      exact (span_le.2 (by rintro _ ⟨j, rfl⟩; exact hn j) : span Ω (Set.range n) ≤ V)
        (span_le_restrictScalars (regAt ξ p) Ω _ hx')
    exact eq_zero_of_mem hc (span_le_restrictScalars (regAt ξ p) Ω _ hx) hxV

end GlobalTheory.CompanionTheory.Ar
