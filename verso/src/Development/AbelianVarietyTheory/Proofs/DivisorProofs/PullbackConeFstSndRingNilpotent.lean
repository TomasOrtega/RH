import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_inf, RingHom.mem_ker, RingHom.mem_ker]`. Rewrite using `[Ideal.mem_bot]`. Conclude with `Subtype.ext (Prod.ext hx.1 hx.2)`.
-/
theorem pullbackCone_ker_fst_inf_ker_snd {A B C : CommRingCat.{0}} (f : A ⟶ C) (g : B ⟶ C) :
    RingHom.ker (CommRingCat.pullbackCone f g).fst.hom ⊓
      RingHom.ker (CommRingCat.pullbackCone f g).snd.hom = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_inf, RingHom.mem_ker, RingHom.mem_ker] at hx
  rw [Ideal.mem_bot]
  exact Subtype.ext (Prod.ext hx.1 hx.2)

/- English proof (translation)
Combine the equalities or inequalities in the calculation `calc I ^ k ≤ (Ideal.comap φ J) ^ k := Ideal.pow_right_mono hIJ k _ ≤ Ideal.comap φ (J ^ k) := Ideal.le_comap_pow φ k _ = RingHom.ker φ := by rw [hJ, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot]`.
-/
theorem pow_le_ker_of_le_comap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (J : Ideal S) (k : ℕ) (hIJ : I ≤ Ideal.comap φ J) (hJ : J ^ k = 0) :
    I ^ k ≤ RingHom.ker φ :=
  calc I ^ k ≤ (Ideal.comap φ J) ^ k := Ideal.pow_right_mono hIJ k
    _ ≤ Ideal.comap φ (J ^ k) := Ideal.le_comap_pow φ k
    _ = RingHom.ker φ := by rw [hJ, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot]

/- English proof (translation)
Introduce and unpack `hf ⟨n, hn⟩ hg ⟨m, hm⟩`. Establish `hbot` using `pullbackCone_ker_fst_inf_ker_snd f g`. Establish `hcomm : ∀ x : (CommRingCat.pullbackCone f g).pt, f.hom ((CommRingCat.pullbackCone f g).fst.hom x) = g.hom ((CommRingCat.pullbackCone f g).snd.hom x)` using `fun x => x.2`. Establish `k1 : RingHom.ker (CommRingCat.pullbackCone f g).fst.hom ≤ Ideal.comap (CommRingCat.pullbackCone f g).snd.hom (RingHom.ker g.hom)`. Introduce `x hx`.

Rewrite `hx` using `[RingHom.mem_ker]`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← hcomm, hx, map_zero]`. Establish `k2 : RingHom.ker (CommRingCat.pullbackCone f g).snd.hom ≤ Ideal.comap (CommRingCat.pullbackCone f g).fst.hom (RingHom.ker f.hom)`. Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hcomm, hx, map_zero]`. Establish `k3 : RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom ≤ Ideal.comap (CommRingCat.pullbackCone f g).fst.hom (RingHom.ker f.hom)`. Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`.

Simplify using `using hx`. Establish `k4 : RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom ≤ Ideal.comap (CommRingCat.pullbackCone f g).snd.hom (RingHom.ker g.hom)`. Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← hcomm]`.

Simplify using `using hx`. Use `⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `a`. Take `⟨b, hb⟩` from `hg (f.hom a)`. Conclude with `⟨⟨(a, b), hb.symm⟩, rfl⟩`.

Use `⟨m + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_succ]`. Conclude with `(Ideal.mul_le_inf).trans (le_inf inf_le_right ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ m k1 hm)))`. Introduce `b`. Take `⟨a, ha⟩` from `hf (g.hom b)`.

Conclude with `⟨⟨(a, b), ha⟩, rfl⟩`. Use `⟨n + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_succ]`. Conclude with `(Ideal.mul_le_inf).trans (le_inf ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ n k2 hn)) inf_le_right)`. Introduce `c`.

Take `⟨a, ha⟩` from `hf c`. Take `⟨b, hb⟩` from `hg c`. Conclude with `⟨⟨(a, b), ha.trans hb.symm⟩, ha⟩`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_add]`.

Conclude with `(Ideal.mul_le_inf).trans (le_inf ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ n k3 hn)) ((inf_le_right).trans (pow_le_ker_of_le_comap _ _ _ m k4 hm)))`.
-/
theorem pullbackCone_fst_snd_ring_nilpotent {A B C : CommRingCat.{0}} (f : A ⟶ C) (g : B ⟶ C) :
    Function.Surjective f.hom → IsNilpotent (RingHom.ker f.hom) → Function.Surjective g.hom →
    IsNilpotent (RingHom.ker g.hom) →
    (Function.Surjective (CommRingCat.pullbackCone f g).fst.hom ∧
        IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).fst.hom)) ∧
      (Function.Surjective (CommRingCat.pullbackCone f g).snd.hom ∧
        IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).snd.hom)) ∧
      (Function.Surjective ((CommRingCat.pullbackCone f g).fst ≫ f).hom ∧
        IsNilpotent (RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom)) := by
  rintro hf ⟨n, hn⟩ hg ⟨m, hm⟩
  have hbot := pullbackCone_ker_fst_inf_ker_snd f g
  have hcomm : ∀ x : (CommRingCat.pullbackCone f g).pt,
      f.hom ((CommRingCat.pullbackCone f g).fst.hom x) =
        g.hom ((CommRingCat.pullbackCone f g).snd.hom x) := fun x => x.2
  have k1 : RingHom.ker (CommRingCat.pullbackCone f g).fst.hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).snd.hom (RingHom.ker g.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomm, hx, map_zero]
  have k2 : RingHom.ker (CommRingCat.pullbackCone f g).snd.hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).fst.hom (RingHom.ker f.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomm, hx, map_zero]
  have k3 : RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).fst.hom (RingHom.ker f.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa using hx
  have k4 : RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).snd.hom (RingHom.ker g.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomm]
    simpa using hx
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a
    obtain ⟨b, hb⟩ := hg (f.hom a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  · refine ⟨m + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_succ]
    exact (Ideal.mul_le_inf).trans
      (le_inf inf_le_right ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ m k1 hm)))
  · intro b
    obtain ⟨a, ha⟩ := hf (g.hom b)
    exact ⟨⟨(a, b), ha⟩, rfl⟩
  · refine ⟨n + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_succ]
    exact (Ideal.mul_le_inf).trans
      (le_inf ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ n k2 hn)) inf_le_right)
  · intro c
    obtain ⟨a, ha⟩ := hf c
    obtain ⟨b, hb⟩ := hg c
    exact ⟨⟨(a, b), ha.trans hb.symm⟩, ha⟩
  · refine ⟨n + m, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_add]
    exact (Ideal.mul_le_inf).trans
      (le_inf ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ n k3 hn))
        ((inf_le_right).trans (pow_le_ker_of_le_comap _ _ _ m k4 hm)))

end GlobalTheory
