import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyWordMemDualWeyl

open MvPolynomial Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.Published

def IsGLSubmodule (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra k A] (g : GL (Fin N) A), ∀ f ∈ M,
    sqAct A N lam g (map (algebraMap k A) f) ∈
      Submodule.span A (map (algebraMap k A) '' (M : Set (MvPolynomial (Fin N × Fin N) k)))

def InducedSimpleLowestAlcove : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (lam : DomWeight N),
    (∀ i j : Fin N, i < j → lam.w i - lam.w j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ (p : ℤ)) →
    nablaSq k N lam ≠ ⊥ ∧
      ∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), M ≤ nablaSq k N lam →
        IsGLSubmodule k N lam M → M = ⊥ ∨ M = nablaSq k N lam

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Establish `hf' : f ∈ Submodule.span R _` using `hf`. Use `clear hf`.

Proceed by induction on `hf' using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨w, rfl⟩` from `hy`. Use `Submodule.subset_span ⟨w, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`.

Consider the case `smul a y _ hy`. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hy`. Unfold `delSq Formalism.GradedWeylDivisibility.weyl`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨w, rfl⟩`. Use `Submodule.subset_span ⟨_, Submodule.subset_span ⟨w, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`.
-/
theorem span_map_delSq (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (N : ℕ) (lam : DomWeight N) :
    Submodule.span A (map φ '' (delSq R N lam : Set (MvPolynomial (Fin N × Fin N) R))) = delSq A N lam := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hf' : f ∈ Submodule.span R _ := hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      refine Submodule.subset_span ⟨w, ?_⟩
      simp only
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ hy
  · unfold delSq Formalism.GradedWeylDivisibility.weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    refine Submodule.subset_span ⟨_, Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

/- English proof (translation)
Introduce `A _ _ g f hf`. Rewrite using `[span_map_delSq]`. Use `(factSqStable A N lam g).2 _ ?_` and prove the remaining obligations. Rewrite using `[← span_map_delSq k A (algebraMap k A)]`. Conclude with `Submodule.subset_span ⟨f, hf, rfl⟩`.
-/
theorem isGLSubmodule_delSq (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) :
    IsGLSubmodule k N lam (delSq k N lam) := by
  intro A _ _ g f hf
  rw [span_map_delSq]
  refine (factSqStable A N lam g).2 _ ?_
  rw [← span_map_delSq k A (algebraMap k A)]
  exact Submodule.subset_span ⟨f, hf, rfl⟩

/- English proof (translation)
Introduce `h`. Establish `hm : Formalism.GradedWeylDivisibility.hw k le_rfl lam.natW ∈ delSq k N lam` using `Submodule.subset_span ⟨[], rfl⟩`. Rewrite `hm` using `[h, Submodule.mem_bot]`. Conclude with `Formalism.GradedWeylDivisibility.hwNe k N N le_rfl lam.natW hm`.
-/
theorem delSq_ne_bot (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) : delSq k N lam ≠ ⊥ := by
  intro h
  have hm : Formalism.GradedWeylDivisibility.hw k le_rfl lam.natW ∈ delSq k N lam := Submodule.subset_span ⟨[], rfl⟩
  rw [h, Submodule.mem_bot] at hm
  exact Formalism.GradedWeylDivisibility.hwNe k N N le_rfl lam.natW hm

/- English proof (translation)
The claim follows from `((h p hp k N lam hl).2 _ (Formalism.GradedWeylDivisibility.weylLeDual k N N le_rfl _ (factNatW N lam).1) (isGLSubmodule_delSq k N lam)).resolve_left (delSq_ne_bot k N lam)`.
-/
theorem delSq_eq_nablaSq_of_simple (h : InducedSimpleLowestAlcove) (p : ℕ) (hp : p.Prime) (k : Type) [Field k]
    [CharP k p] (N : ℕ) (lam : DomWeight N)
    (hl : ∀ i j : Fin N, i < j → lam.w i - lam.w j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ (p : ℤ)) :
    delSq k N lam = nablaSq k N lam :=
  ((h p hp k N lam hl).2 _ (Formalism.GradedWeylDivisibility.weylLeDual k N N le_rfl _ (factNatW N lam).1)
    (isGLSubmodule_delSq k N lam)).resolve_left (delSq_ne_bot k N lam)

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Establish `hk` using `delSq_eq_nablaSq_of_simple h p hp (ZMod p) N lam hl`. Establish `hsurj : Function.Surjective (Int.castRingHom (ZMod p))` using `ZMod.intCast_surjective`. Establish `himg : ∀ F ∈ delSq (ZMod p) N lam, ∃ w ∈ delSq ℤ N lam, map (Int.castRingHom (ZMod p)) w = F`. Introduce `F hF`.

Rewrite `hF` using `[← span_map_delSq ℤ (ZMod p) (Int.castRingHom (ZMod p))]`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem y hy => exact hy`. Consider the case `zero => exact ⟨0, zero_mem _, map_zero _⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨a, ha, rfl⟩` from `hy`. Take `⟨b, hb, rfl⟩` from `hz`. Conclude with `⟨a + b, add_mem ha hb, map_add _ _ _⟩`. Consider the case `smul a y _ hy`. Take `⟨b, hb, rfl⟩` from `hy`.

Take `⟨z, rfl⟩` from `hsurj a`. Use `⟨z • b, Submodule.smul_mem _ _ hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`. Establish `hle : nablaSq ℤ N lam ≤ delSq ℤ N lam ⊔ Ideal.span {(p : ℤ)} • nablaSq ℤ N lam`. Introduce `f hf`.

Establish `h1 : map (Int.castRingHom (ZMod p)) f ∈ delSq (ZMod p) N lam`. Rewrite using `[hk]`. Conclude with `Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ N N _ f hf`. Take `⟨w, hw, hwf⟩` from `himg _ h1`. Establish `h2 : (C (p : ℤ) : MvPolynomial (Fin N × Fin N) ℤ) ∣ f - w`.

Rewrite using `[C_dvd_iff_zmod, map_sub, hwf, sub_self]`. Take `⟨u, hu⟩` from `h2`. Establish `hw' : w ∈ nablaSq ℤ N lam` using `Formalism.GradedWeylDivisibility.weylLeDual ℤ N N le_rfl _ (factNatW N lam).1 hw`. Establish `hu' : u ∈ nablaSq ℤ N lam`. Use `Formalism.GradedWeylDivisibility.dualWeylSat ℤ N N _ (p : ℤ) u (by exact_mod_cast hp.ne_zero) ?_` and prove the remaining obligations.

Rewrite using `[smul_eq_C_mul, ← hu]`. Conclude with `sub_mem hf hw'`. Establish `e : f = w + (p : ℤ) • u` using `by rw [smul_eq_C_mul, ← hu]; ring`. Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup hw (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hu')`.

Take `⟨c, hc1, hc⟩` from `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := Ideal.span {(p : ℤ)}) (N := delSq ℤ N lam) (N' := nablaSq ℤ N lam) (P := nablaSq ℤ N lam) (GlobalTheory.WeylDuality.dualWeyl_int_fg N N lam.natW) le_rfl hle`. Use `⟨c, fun hd => ?_, fun f hf => hc (Submodule.smul_mem_pointwise_smul _ _ _ hf)⟩` and prove the remaining obligations. Establish `: (p : ℤ) ∣ 1`. Use `dvd_sub hd (Ideal.mem_span_singleton.mp hc1)` as an intermediate fact. Simplify using `using this`.

Conclude with `hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)`.
-/
theorem exists_smul_mem_delSq_of_simple (h : InducedSimpleLowestAlcove) (p : ℕ) (hp : p.Prime) (N : ℕ)
    (lam : DomWeight N)
    (hl : ∀ i j : Fin N, i < j → lam.w i - lam.w j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ (p : ℤ)) :
    ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ ∀ f ∈ nablaSq ℤ N lam, c • f ∈ delSq ℤ N lam := by
  have := Fact.mk hp
  have hk := delSq_eq_nablaSq_of_simple h p hp (ZMod p) N lam hl
  have hsurj : Function.Surjective (Int.castRingHom (ZMod p)) := ZMod.intCast_surjective
  have himg : ∀ F ∈ delSq (ZMod p) N lam, ∃ w ∈ delSq ℤ N lam, map (Int.castRingHom (ZMod p)) w = F := by
    intro F hF
    rw [← span_map_delSq ℤ (ZMod p) (Int.castRingHom (ZMod p))] at hF
    induction hF using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
    | smul a y _ hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      obtain ⟨z, rfl⟩ := hsurj a
      refine ⟨z • b, Submodule.smul_mem _ _ hb, ?_⟩
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
  have hle : nablaSq ℤ N lam ≤ delSq ℤ N lam ⊔ Ideal.span {(p : ℤ)} • nablaSq ℤ N lam := by
    intro f hf
    have h1 : map (Int.castRingHom (ZMod p)) f ∈ delSq (ZMod p) N lam := by
      rw [hk]; exact Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ N N _ f hf
    obtain ⟨w, hw, hwf⟩ := himg _ h1
    have h2 : (C (p : ℤ) : MvPolynomial (Fin N × Fin N) ℤ) ∣ f - w := by
      rw [C_dvd_iff_zmod, map_sub, hwf, sub_self]
    obtain ⟨u, hu⟩ := h2
    have hw' : w ∈ nablaSq ℤ N lam := Formalism.GradedWeylDivisibility.weylLeDual ℤ N N le_rfl _ (factNatW N lam).1 hw
    have hu' : u ∈ nablaSq ℤ N lam := by
      refine Formalism.GradedWeylDivisibility.dualWeylSat ℤ N N _ (p : ℤ) u (by exact_mod_cast hp.ne_zero) ?_
      rw [smul_eq_C_mul, ← hu]
      exact sub_mem hf hw'
    have e : f = w + (p : ℤ) • u := by rw [smul_eq_C_mul, ← hu]; ring
    rw [e]
    exact Submodule.add_mem_sup hw (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hu')
  obtain ⟨c, hc1, hc⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {(p : ℤ)}) (N := delSq ℤ N lam) (N' := nablaSq ℤ N lam) (P := nablaSq ℤ N lam)
    (GlobalTheory.WeylDuality.dualWeyl_int_fg N N lam.natW) le_rfl hle
  refine ⟨c, fun hd => ?_, fun f hf => hc (Submodule.smul_mem_pointwise_smul _ _ _ hf)⟩
  have : (p : ℤ) ∣ 1 := by
    have := dvd_sub hd (Ideal.mem_span_singleton.mp hc1)
    simpa using this
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

/- English proof (translation)
Introduce `N lam p hp hs f hf`. Take `⟨c, hc, hcf⟩` from `exists_smul_mem_delSq_of_simple h p hp N lam (by`. Introduce `i j hij`. Establish `hN : 0 < N` using `Nat.lt_of_le_of_lt (Nat.zero_le _) i.2`. Rewrite `hs` using `[DomWeight.spread, dif_pos hN]`.

Establish `h1 : lam.w i ≤ lam.w ⟨0, hN⟩` using `lam.anti (Fin.le_def.mpr (Nat.zero_le _))`. Establish `h2 : lam.w ⟨N - 1, by omega⟩ ≤ lam.w j` using `lam.anti (Fin.le_def.mpr (by have := j.2; simp only; omega))`. Use `j.2` as an intermediate fact. Use the proof step `omega)`. Conclude with `⟨c, hc, hcf f hf⟩`.
-/
theorem weylDualWeylLatticesAgree_of_lowest_alcove (h : InducedSimpleLowestAlcove) : NablaMemDeltaLocallyAtLargePrime := by
  intro N lam p hp hs f hf
  obtain ⟨c, hc, hcf⟩ := exists_smul_mem_delSq_of_simple h p hp N lam (by
    intro i j hij
    have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
    rw [DomWeight.spread, dif_pos hN] at hs
    have h1 : lam.w i ≤ lam.w ⟨0, hN⟩ := lam.anti (Fin.le_def.mpr (Nat.zero_le _))
    have h2 : lam.w ⟨N - 1, by omega⟩ ≤ lam.w j := lam.anti (Fin.le_def.mpr (by have := j.2; simp only; omega))
    have := j.2
    omega)
  exact ⟨c, hc, hcf f hf⟩

end GlobalTheory.Published
