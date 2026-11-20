import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc UpperTheory.V.Af.GlobalFixedVectors Matrix

/- English proof (translation)
Simplify using `[Kc, Subgroup.mem_iInf]`.
-/
private theorem mem_Kc {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} :
    k ∈ Kc c ↔ ∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := by
  simp [Kc, Subgroup.mem_iInf]

/- English proof (translation)
Use `mem_Ohat.2 fun w => ?_` and prove the remaining obligations. Take `⟨g, -, hg⟩` from `mem_Kc.1 hk w`. Establish `e` using `congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) hg`. Express the relevant statement in the definitionally equal form `((g i j : w.adicCompletionIntegers F) : w.adicCompletion F) = pLoc F w (k i j) at e`. Rewrite using `[← e]`.

Conclude with `(g i j).2`.
-/
private theorem entry_Kc {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) (i j : Fin 2) :
    k i j ∈ UpperTheory.V.Af.Ohat F := by
  refine mem_Ohat.2 fun w => ?_
  obtain ⟨g, -, hg⟩ := mem_Kc.1 hk w
  have e := congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) hg
  change ((g i j : w.adicCompletionIntegers F) : w.adicCompletion F) = pLoc F w (k i j) at e
  rw [← e]
  exact (g i j).2

/- English proof (translation)
Set `A : Matrix (Fin 2) (Fin 2) (UpperTheory.V.Af.Ohat F)` to `fun i j => ⟨k i j, entry_Kc hk i j⟩`. Set `B : Matrix (Fin 2) (Fin 2) (UpperTheory.V.Af.Ohat F)` to `fun i j => ⟨(k⁻¹ : GF F) i j, entry_Kc (inv_mem hk) i j⟩`. Establish `hA : (UpperTheory.V.Af.Ohat F).subtype.mapMatrix A = k.val` using `rfl`. Establish `hB : (UpperTheory.V.Af.Ohat F).subtype.mapMatrix B = (k⁻¹ : GF F).val` using `rfl`. Establish `hinj : Function.Injective ((UpperTheory.V.Af.Ohat F).subtype.mapMatrix (m` using `Fin 2)) := Matrix.map_injective Subtype.val_injective`.

Use `⟨⟨A, B, hinj ?_, hinj ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_one, hA, hB, Units.mul_inv]`. Rewrite using `[map_mul, map_one, hA, hB, Units.inv_mul]`. Use `haveI : Subsingleton (UpperTheory.V.Af.Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(UpperTheory.V.Af.Ohat F))}) := Ideal.Quotient.subsingleton_iff.2 (by simp)`. Use extensionality with `i j`.

Conclude with `Subsingleton.elim _ _`. Conclude with `Units.ext hA`.
-/
private theorem Kc_le {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) : k ∈ KLev F 2 1 := by
  let A : Matrix (Fin 2) (Fin 2) (UpperTheory.V.Af.Ohat F) := fun i j => ⟨k i j, entry_Kc hk i j⟩
  let B : Matrix (Fin 2) (Fin 2) (UpperTheory.V.Af.Ohat F) := fun i j => ⟨(k⁻¹ : GF F) i j, entry_Kc (inv_mem hk) i j⟩
  have hA : (UpperTheory.V.Af.Ohat F).subtype.mapMatrix A = k.val := rfl
  have hB : (UpperTheory.V.Af.Ohat F).subtype.mapMatrix B = (k⁻¹ : GF F).val := rfl
  have hinj : Function.Injective ((UpperTheory.V.Af.Ohat F).subtype.mapMatrix (m := Fin 2)) :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, ?_, ?_⟩
  · rw [map_mul, map_one, hA, hB, Units.mul_inv]
  · rw [map_mul, map_one, hA, hB, Units.inv_mul]
  · haveI : Subsingleton (UpperTheory.V.Af.Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(UpperTheory.V.Af.Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · exact Units.ext hA

/- English proof (translation)
Introduce `F _ _ V _ _ ρ hρ c x hc`. Establish `key : ∀ S : Finset (Pl F), (∀ k ∈ KAway 2 1 S, k ∈ Kc c → ρ k x = x) → (∀ k ∈ KAway 2 1 ∅, k ∈ Kc c → ρ k x = x)`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact id`.

Consider the case `insert w S hw ih`. Introduce `h`. Use `ih fun k hk hl => ?_` and prove the remaining obligations. Rewrite `hl` using `[mem_Kc]`. Establish `h1` using `loc_mem w (mem_KAway.1 hk).1`.

Establish `h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 1 (insert w S)`. Use `mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩` and prove the remaining obligations. Distinguish the cases in `huw : u = w`. Substitute `huw` using the available equality. Simplify using `[pLoc_locGL]`.

Simplify using `[pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]`. Establish `h3 : ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) x = x` using `hc w _ (hl w)`. Establish `h4` using `h _ h2 (mem_Kc.2 fun v => by`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality.

Simplify using `[pLoc_locGL]`. Simplify `hl v)` using `[pLoc_locGL_of_ne hv]`. Rewrite `h4` using `[← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3]`. Then use the resulting hypothesis. Take `⟨S, hS⟩` from `exists_KAway_subset (M := 1) ((hρ x).mem_nhds (by simp))`. Introduce `k hk`.

Conclude with `key S (fun k hk _ => hS hk) k (mem_KAway.2 ⟨Kc_le hk, by simp⟩) hk`.
-/
theorem UpperTheory.V.Sd.Wc.fixGlob :
    UpperTheory.V.Sd.Wc.FixGlob := by
  classical
  intro F _ _ V _ _ ρ hρ c x hc
  have key : ∀ S : Finset (Pl F),
      (∀ k ∈ KAway 2 1 S, k ∈ Kc c → ρ k x = x) → (∀ k ∈ KAway 2 1 ∅, k ∈ Kc c → ρ k x = x) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      intro h
      refine ih fun k hk hl => ?_
      rw [mem_Kc] at hl
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 1 (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) x = x := hc w _ (hl w)
      have h4 := h _ h2 (mem_Kc.2 fun v => by
        by_cases hv : v = w
        · subst hv; simp [pLoc_locGL]
        · simpa [pLoc_locGL_of_ne hv] using hl v)
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) ((hρ x).mem_nhds (by simp))
  intro k hk
  exact key S (fun k hk _ => hS hk) k (mem_KAway.2 ⟨Kc_le hk, by simp⟩) hk
