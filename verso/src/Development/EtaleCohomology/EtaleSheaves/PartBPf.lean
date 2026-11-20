import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.PartBPf

/- English proof (translation)
Establish `h1 : (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) x ∈ (I.map (βP I P)).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)` using `Ideal.mem_map_of_mem _ hx`. Rewrite `h1` using `[Ideal.map_map]`. Establish `h2 : (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e).comp (βP I P) = algebraMap B (Localization (S I e.1))`. Use extensionality with `b`. Both sides reduce to the same expression.

Rewrite `h1` using `[h2]`. Conclude with `h1`.
-/
theorem comp_mem {B : Type} [CommRing B] (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (x : PiLocalization₂ I P)
    (hx : x ∈ I.map (βP I P)) (e : P.1) :
    x e ∈ I.map (algebraMap B (Localization (S I e.1))) := by
  have h1 : (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) x ∈
      (I.map (βP I P)).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) :=
    Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_map] at h1
  have h2 : (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e).comp (βP I P) =
      algebraMap B (Localization (S I e.1)) := by
    ext b; rfl
  rw [h2] at h1
  exact h1

/- English proof (translation)
Take `⟨⟨⟨i, hi⟩, ⟨s, hs⟩⟩, h⟩` from `(IsLocalization.mem_map_algebraMap_iff (S I e) _).1 hy`. Simplify using `only at h`. Establish `hsi : s + i ∈ S I e`. Take `⟨t, ht⟩` from `hs`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Establish `: Ideal.Quotient.mk I i = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 hi`. Rewrite using `[map_add, this, add_zero]`. Conclude with `ht`. Establish `hu : IsUnit ((1 + y) * algebraMap B _ s)`. Rewrite using `[add_mul, one_mul, h, ← map_add]`.

Conclude with `IsLocalization.map_units (Localization (S I e)) ⟨s + i, hsi⟩`. Conclude with `isUnit_of_mul_isUnit_left hu`.
-/
theorem comp_unit {B : Type} [CommRing B] (I : Ideal B) (e : B ⧸ I) (y : Localization (S I e))
    (hy : y ∈ I.map (algebraMap B (Localization (S I e)))) : IsUnit (1 + y) := by
  obtain ⟨⟨⟨i, hi⟩, ⟨s, hs⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff (S I e) _).1 hy
  simp only at h
  have hsi : s + i ∈ S I e := by
    obtain ⟨t, ht⟩ := hs
    refine ⟨t, ?_⟩
    have : Ideal.Quotient.mk I i = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hi
    rw [map_add, this, add_zero]; exact ht
  have hu : IsUnit ((1 + y) * algebraMap B _ s) := by
    rw [add_mul, one_mul, h, ← map_add]
    exact IsLocalization.map_units (Localization (S I e)) ⟨s + i, hsi⟩
  exact isUnit_of_mul_isUnit_left hu

/- English proof (translation)
Introduce `B _ I P x hx`. Rewrite using `[Pi.isUnit_iff]`. Introduce `e`. Conclude with `comp_unit I e.1 (x e) (comp_mem I P x hx e)`.
-/
theorem PartB_of : LateralTheory.E.PartDiagCut.PartB := by
  intro B _ I P x hx
  rw [Pi.isUnit_iff]
  intro e
  exact comp_unit I e.1 (x e) (comp_mem I P x hx e)

end LateralTheory.E.PartBPf
