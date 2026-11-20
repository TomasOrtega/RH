import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.ExtensionByZero

private noncomputable def ext0 (C : DC) (s : ℤ) (a : C.A 0 s) : C.Tot
  | 0, t => (Pi.single s a : ∀ t, C.A 0 t) t
  | _ + 1, _ => 0

/- English proof (translation)
The claim follows from `Pi.single_eq_same (M := fun t => C.A 0 t) s a`.
-/
private theorem extByZero_same (C : DC) (s : ℤ) (a : C.A 0 s) : ext0 C s a 0 s = a :=
  Pi.single_eq_same (M := fun t => C.A 0 t) s a

/- English proof (translation)
The claim follows from `Pi.single_eq_of_ne (M := fun t => C.A 0 t) h a`.
-/
private theorem unitCharacterExtendByZero_ne_zero_of_isUnit (C : DC) (s : ℤ) (a : C.A 0 s) {t : ℤ} (h : t ≠ s) : ext0 C s a 0 t = 0 :=
  Pi.single_eq_of_ne (M := fun t => C.A 0 t) h a

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem extByZero_succ (C : DC) (s : ℤ) (a : C.A 0 s) (p : ℕ) (t : ℤ) : ext0 C s a (p + 1) t = 0 := rfl

/- English proof (translation)
Introduce `p t h`. Break down `p with _ | p` into its components or cases. Conclude with `unitCharacterExtendByZero_ne_zero_of_isUnit C s a (fun e => h (by simp [e]))`. Both sides reduce to the same expression.
-/
private theorem extByZero_degree (C : DC) (s : ℤ) (a : C.A 0 s) : C.Deg s (ext0 C s a) := by
  intro p t h
  rcases p with _ | p
  · exact unitCharacterExtendByZero_ne_zero_of_isUnit C s a (fun e => h (by simp [e]))
  · rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
private theorem d_idx (C : DC) (f : ∀ t, C.A 0 t) {u s : ℤ} (t : ℤ) (h : u = s) :
    C.d 0 u t (f u) = C.d 0 s t (f s) := by
  subst h; rfl

end UpperTheory.ExtensionByZero

open UpperTheory.ExtensionByZero in
/- English proof (translation)
Introduce `C C' Φ h0 h0' hT s a y hda hΦ`. Establish `hD : C.D (s + 1) (ext0 C (s + 1) a) = 0`. Use function extensionality and compare the values at `p t`. Break down `p with _ | p` into its components or cases. Express the relevant statement in the definitionally equal form `C.d 0 (t - 1) t (ext0 C (s + 1) a 0 (t - 1)) = 0`.

Distinguish the cases in `h : t - 1 = s + 1`. Take `rfl : t = s + 1 + 1` from `by omega`. Rewrite using `[d_idx C (ext0 C (s + 1) a 0) _ h, extByZero_same]`. Conclude with `hda`. Rewrite using `[unitCharacterExtendByZero_ne_zero_of_isUnit C _ a h, map_zero]`.

Express the relevant statement in the definitionally equal form `C.d (p + 1) (t - 1) t (ext0 C (s + 1) a (p + 1) (t - 1)) + (s + 1 + 1).negOnePow • C.δ p t (ext0 C (s + 1) a p t) = 0`. Rewrite using `[extByZero_succ, map_zero, zero_add]`. Break down `p with _ | p` into its components or cases. Rewrite using `[h0, smul_zero]`. Rewrite using `[extByZero_succ, map_zero, smul_zero]`.

Establish `hE : Φ.tot (ext0 C (s + 1) a) = C'.D s (ext0 C' s y)`. Use function extensionality and compare the values at `p t`. Break down `p with _ | p` into its components or cases. Express the relevant statement in the definitionally equal form `Φ 0 t (ext0 C (s + 1) a 0 t) = C'.d 0 (t - 1) t (ext0 C' s y 0 (t - 1))`. Distinguish the cases in `h : t = s + 1`.

Substitute `h` using the available equality. Rewrite using `[d_idx C' (ext0 C' s y 0) _ (by omega : s + 1 - 1 = s), extByZero_same, extByZero_same]`. Conclude with `hΦ`. Rewrite using `[unitCharacterExtendByZero_ne_zero_of_isUnit C _ a h, unitCharacterExtendByZero_ne_zero_of_isUnit C' _ y (fun e => h (by omega)), map_zero, map_zero]`. Express the relevant statement in the definitionally equal form `Φ (p + 1) t (ext0 C (s + 1) a (p + 1) t) = C'.d (p + 1) (t - 1) t (ext0 C' s y (p + 1) (t - 1)) + (s + 1).negOnePow • C'.δ p t (ext0 C' s y p t)`.

Rewrite using `[extByZero_succ, extByZero_succ, map_zero, map_zero, zero_add]`. Break down `p with _ | p` into its components or cases. Rewrite using `[h0', smul_zero]`. Rewrite using `[extByZero_succ, map_zero, smul_zero]`. Take `⟨a', y', -, -, h1, h2⟩` from `hT s (ext0 C (s + 1) a) (ext0 C' s y) (extByZero_degree C _ a) (extByZero_degree C' _ y) hD hE`.

Use `⟨a' 0 s, y' 0 (s - 1), ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrFun h1 0) (s + 1)`. Express the relevant statement in the definitionally equal form `C.d 0 (s + 1 - 1) (s + 1) (a' 0 (s + 1 - 1)) = ext0 C (s + 1) a 0 (s + 1) at h`. Rewrite `h` using `[d_idx C (a' 0) _ (by omega : s + 1 - 1 = s), extByZero_same]`. Conclude with `h`.

Establish `h` using `congrFun (congrFun h2 0) s`. Rewrite `h` using `[show ext0 C' s y 0 s = y from extByZero_same C' s y]`. Conclude with `h`.
-/
theorem UpperTheory.columnExact_zero_of_totalExact_of_vertical_zero :
    ∀ (C C' : DC) (Φ : C.Hom C'), (∀ s x, C.δ 0 s x = 0) → (∀ s x, C'.δ 0 s x = 0) → Φ.TotEx → Φ.ColEx 0 := by
  intro C C' Φ h0 h0' hT s a y hda hΦ
  have hD : C.D (s + 1) (ext0 C (s + 1) a) = 0 := by
    funext p t
    rcases p with _ | p
    · change C.d 0 (t - 1) t (ext0 C (s + 1) a 0 (t - 1)) = 0
      by_cases h : t - 1 = s + 1
      · obtain rfl : t = s + 1 + 1 := by omega
        rw [d_idx C (ext0 C (s + 1) a 0) _ h, extByZero_same]
        exact hda
      · rw [unitCharacterExtendByZero_ne_zero_of_isUnit C _ a h, map_zero]
    · change C.d (p + 1) (t - 1) t (ext0 C (s + 1) a (p + 1) (t - 1)) +
        (s + 1 + 1).negOnePow • C.δ p t (ext0 C (s + 1) a p t) = 0
      rw [extByZero_succ, map_zero, zero_add]
      rcases p with _ | p
      · rw [h0, smul_zero]
      · rw [extByZero_succ, map_zero, smul_zero]
  have hE : Φ.tot (ext0 C (s + 1) a) = C'.D s (ext0 C' s y) := by
    funext p t
    rcases p with _ | p
    · change Φ 0 t (ext0 C (s + 1) a 0 t) = C'.d 0 (t - 1) t (ext0 C' s y 0 (t - 1))
      by_cases h : t = s + 1
      · subst h
        rw [d_idx C' (ext0 C' s y 0) _ (by omega : s + 1 - 1 = s), extByZero_same, extByZero_same]
        exact hΦ
      · rw [unitCharacterExtendByZero_ne_zero_of_isUnit C _ a h, unitCharacterExtendByZero_ne_zero_of_isUnit C' _ y (fun e => h (by omega)), map_zero, map_zero]
    · change Φ (p + 1) t (ext0 C (s + 1) a (p + 1) t) =
        C'.d (p + 1) (t - 1) t (ext0 C' s y (p + 1) (t - 1)) +
          (s + 1).negOnePow • C'.δ p t (ext0 C' s y p t)
      rw [extByZero_succ, extByZero_succ, map_zero, map_zero, zero_add]
      rcases p with _ | p
      · rw [h0', smul_zero]
      · rw [extByZero_succ, map_zero, smul_zero]
  obtain ⟨a', y', -, -, h1, h2⟩ :=
    hT s (ext0 C (s + 1) a) (ext0 C' s y) (extByZero_degree C _ a) (extByZero_degree C' _ y) hD hE
  refine ⟨a' 0 s, y' 0 (s - 1), ?_, ?_⟩
  · have h := congrFun (congrFun h1 0) (s + 1)
    change C.d 0 (s + 1 - 1) (s + 1) (a' 0 (s + 1 - 1)) = ext0 C (s + 1) a 0 (s + 1) at h
    rw [d_idx C (a' 0) _ (by omega : s + 1 - 1 = s), extByZero_same] at h
    exact h
  · have h := congrFun (congrFun h2 0) s
    rw [show ext0 C' s y 0 s = y from extByZero_same C' s y] at h
    exact h
