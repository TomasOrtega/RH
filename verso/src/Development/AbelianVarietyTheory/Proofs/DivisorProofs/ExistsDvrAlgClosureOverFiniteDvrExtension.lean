import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingDvrContainingFinsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationLeCardOfSpanStatement
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `V W _ _ _ _ _ _ hV hW io hio hinj F _ _ _ _ hcomp`. Take `⟨hVd, -, hV0⟩` from `(GlobalTheory.LN.cDvr_iff V).1 hV`. Take `⟨hWd, -, -⟩` from `(GlobalTheory.LN.cDvr_iff W).1 hW`. Use `set φV : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V _) with hφV`. Use `set φW : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hφW`.

Establish `hφWinj : Function.Injective φW` using `(algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)`. Establish `hφVinj : Function.Injective φV` using `(algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _)`. Use `haveI : CharZero F := (RingHom.charZero_iff hφVinj).1 hV0`. Establish `hc : ∀ v, φW (io v) = φV v` using `hcomp`. Use `letI := io.toAlgebra`.

Use `haveI : Module.Finite V W := hio`. Take `⟨n, gens, hspan⟩` from `Module.Finite.exists_fin (R := V) (M := W)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Introduce `T' hT' f hf hirr`. Use `set s : Finset F := Finset.univ.image (fun i => φW (gens i)) with hs`.

Establish `hcard : s.card ≤ n`. Combine the equalities or inequalities in the displayed calculation. Establish `K1 : ∀ w : W, φW w ∈ Submodule.span T' (s : Set F)`. Introduce `w`. Establish `hw : w ∈ Submodule.span V (Set.range gens)` using `by rw [hspan]; trivial`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `Submodule.subset_span (by simp [hs])`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul v x _ hx`. Establish `: φW (v • x) = (f v) • φW x`. Rewrite using `[Algebra.smul_def, map_mul, Subring.smul_def, smul_eq_mul, hf]`.

Conclude with `congrArg (· * φW x) (hc v)`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `h1 : (1 : F) ∈ Submodule.span T' (s : Set F)` using `by simpa using K1 1`. Establish `hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)`.

Introduce `x hx y hy`. Simplify using `only [hs, Finset.mem_image, Finset.mem_univ, true_and] at hx hy`. Take `⟨i, rfl⟩` from `hx`. Take `⟨j, rfl⟩` from `hy`. Rewrite using `[← map_mul]`.

Conclude with `K1 _`. Take `⟨T'', hT'', hle, hsT, hdom, hden⟩` from `GlobalTheory.T.exists_dominating_dvr_containing_finset F T' hT' s h1 hmul`. Establish `K2 : ∀ x ∈ Submodule.span T' (s : Set F), x ∈ T''`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact hsT x hx`. Consider the case `zero => exact T''.zero_mem`. Consider the case `add x y _ _ hx hy => exact T''.add_mem hx hy`. Consider the case `smul t x _ hx => rw [Subring.smul_def, smul_eq_mul]`. Conclude with `T''.mul_mem (hle t.2) hx`.

Set `g : W →+* T''` to `φW.codRestrict T'' (fun w => K2 _ (K1 w))`. Establish `hg : ∀ w, (g w : F) = φW w` using `fun w => rfl`. Establish `hginj : Function.Injective g` using `fun a b h => hφWinj (by simpa [hg] using congrArg Subtype.val h)`. Use `haveI := hT''`. Take `⟨πV, hπV⟩` from `IsDiscreteValuationRing.exists_irreducible V`.

Establish `hfπ` using `hirr πV hπV`. Take `⟨ϖ, hϖ, e', he1, he2, hassoc⟩` from `GlobalTheory.T.exists_irreducible_pow_associated_le_card_of_span F T' T'' hT' hT'' hle hdom s hden (f πV) hfπ`. Take `⟨πW, hπW⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Establish `hioπ : io πV ≠ 0` using `fun h => hπV.ne_zero (hinj (by rw [h, map_zero]))`. Take `⟨a, ha⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hioπ hπW`.

Establish `hgπ : g πW ≠ 0` using `fun h => hπW.ne_zero (hginj (by rw [h, map_zero]))`. Take `⟨k, hk⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hgπ hϖ`. Establish `hgio : g (io πV) = Subring.inclusion hle (f πV)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hg, hc]`.

Conclude with `(hf πV).symm`. Establish `hA : Associated (ϖ ^ e') (ϖ ^ (k * a))`. Establish `h2 : Associated (g (io πV)) ((g πW) ^ a)`. Rewrite using `[← map_pow]`. Conclude with `ha.map g`.

Rewrite `h2` using `[hgio]`. Rewrite using `[pow_mul]`. Conclude with `hassoc.symm.trans (h2.trans hk.pow_pow)`. Establish `hka : e' = k * a`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `(pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hA.dvd`. Conclude with `(pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hA.symm.dvd`. Establish `hk0 : k ≠ 0` using `by rintro rfl; simp at hka; omega`. Establish `ha0 : a ≠ 0` using `by rintro rfl; simp at hka; omega`. Use `⟨T'', hT'', g, k, hle, fun w => rfl, Nat.one_le_iff_ne_zero.2 hk0, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Introduce `π hπ`. Conclude with `⟨ϖ, hϖ, ((IsDiscreteValuationRing.associated_of_irreducible W hπ hπW).map g).trans hk⟩`.
-/
theorem exists_dvr_over_finite_ext : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr V → GlobalTheory.LN.CDvr W → ∀ io : V →+* W, io.Finite → Function.Injective io → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∃ N : ℕ, ∀ (T' : Subring F) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v, (f v : F) = algebraMap (FractionRing V) F (algebraMap V _ v)) → (∀ π, Irreducible π → Irreducible (f π)) → ∃ (T'' : Subring F) (_ : IsDiscreteValuationRing T'') (g : W →+* T'') (e : ℕ), T' ≤ T'' ∧ (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ ∀ π, Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ Associated (g π) (ϖ ^ e) := by
  classical
  intro V W _ _ _ _ _ _ hV hW io hio hinj F _ _ _ _ hcomp
  obtain ⟨hVd, -, hV0⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨hWd, -, -⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  set φV : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V _) with hφV
  set φW : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hφW
  have hφWinj : Function.Injective φW :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  have hφVinj : Function.Injective φV :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _)
  haveI : CharZero F := (RingHom.charZero_iff hφVinj).1 hV0
  have hc : ∀ v, φW (io v) = φV v := hcomp
  letI := io.toAlgebra
  haveI : Module.Finite V W := hio
  obtain ⟨n, gens, hspan⟩ := Module.Finite.exists_fin (R := V) (M := W)
  refine ⟨n, ?_⟩
  intro T' hT' f hf hirr
  set s : Finset F := Finset.univ.image (fun i => φW (gens i)) with hs
  have hcard : s.card ≤ n := by
    calc s.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have K1 : ∀ w : W, φW w ∈ Submodule.span T' (s : Set F) := by
    intro w
    have hw : w ∈ Submodule.span V (Set.range gens) := by rw [hspan]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span (by simp [hs])
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul v x _ hx =>
      have : φW (v • x) = (f v) • φW x := by
        rw [Algebra.smul_def, map_mul, Subring.smul_def, smul_eq_mul, hf]
        exact congrArg (· * φW x) (hc v)
      rw [this]; exact Submodule.smul_mem _ _ hx
  have h1 : (1 : F) ∈ Submodule.span T' (s : Set F) := by simpa using K1 1
  have hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F) := by
    intro x hx y hy
    simp only [hs, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy
    rw [← map_mul]; exact K1 _
  obtain ⟨T'', hT'', hle, hsT, hdom, hden⟩ := GlobalTheory.T.exists_dominating_dvr_containing_finset F T' hT' s h1 hmul
  have K2 : ∀ x ∈ Submodule.span T' (s : Set F), x ∈ T'' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hsT x hx
    | zero => exact T''.zero_mem
    | add x y _ _ hx hy => exact T''.add_mem hx hy
    | smul t x _ hx => rw [Subring.smul_def, smul_eq_mul]; exact T''.mul_mem (hle t.2) hx
  let g : W →+* T'' := φW.codRestrict T'' (fun w => K2 _ (K1 w))
  have hg : ∀ w, (g w : F) = φW w := fun w => rfl
  have hginj : Function.Injective g := fun a b h => hφWinj (by simpa [hg] using congrArg Subtype.val h)
  haveI := hT''
  obtain ⟨πV, hπV⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hfπ := hirr πV hπV
  obtain ⟨ϖ, hϖ, e', he1, he2, hassoc⟩ := GlobalTheory.T.exists_irreducible_pow_associated_le_card_of_span F T' T'' hT' hT'' hle hdom s hden (f πV) hfπ
  obtain ⟨πW, hπW⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hioπ : io πV ≠ 0 := fun h => hπV.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.associated_pow_irreducible hioπ hπW
  have hgπ : g πW ≠ 0 := fun h => hπW.ne_zero (hginj (by rw [h, map_zero]))
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hgπ hϖ
  have hgio : g (io πV) = Subring.inclusion hle (f πV) := by
    apply Subtype.ext
    rw [hg, hc]
    exact (hf πV).symm
  have hA : Associated (ϖ ^ e') (ϖ ^ (k * a)) := by
    have h2 : Associated (g (io πV)) ((g πW) ^ a) := by
      rw [← map_pow]; exact ha.map g
    rw [hgio] at h2
    rw [pow_mul]
    exact hassoc.symm.trans (h2.trans hk.pow_pow)
  have hka : e' = k * a := by
    apply le_antisymm
    · exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hA.dvd
    · exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hA.symm.dvd
  have hk0 : k ≠ 0 := by rintro rfl; simp at hka; omega
  have ha0 : a ≠ 0 := by rintro rfl; simp at hka; omega
  refine ⟨T'', hT'', g, k, hle, fun w => rfl, Nat.one_le_iff_ne_zero.2 hk0, ?_, ?_⟩
  · calc k ≤ k * a := Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero ha0)
      _ = e' := hka.symm
      _ ≤ s.card := he2
      _ ≤ n := hcard
  · intro π hπ
    exact ⟨ϖ, hϖ, ((IsDiscreteValuationRing.associated_of_irreducible W hπ hπW).map g).trans hk⟩

end GlobalTheory
