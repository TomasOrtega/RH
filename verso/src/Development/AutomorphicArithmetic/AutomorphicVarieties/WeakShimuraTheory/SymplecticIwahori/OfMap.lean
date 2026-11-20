import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

noncomputable section

open IsLocalRing Polynomial UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws.Pp

def SpTri {ι A C : Type} [CommRing A] [CommRing C] (M : ι → M4 A) (P : ι → Fin 4 → A[X]) (φ : A →+* C) (u : M4 C) : Prop :=
  IsGSp 1 u ∧ ∀ g, IsUp (adj u * (M g).map φ * u) ∧ ∀ i, (P g i).eval₂ φ ((adj u * (M g).map φ * u) i i) = 0

def Dist {A : Type} [CommRing A] (I : Ideal A) (p : A[X]) : Prop := p.Monic ∧ ∀ n < p.natDegree, p.coeff n ∈ I

/- English proof (translation)
Use `⟨?_, fun _ => ⟨fun i j _ => by simp, fun i => by simp⟩⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]`.
-/
example {A : Type} [CommRing A] : SpTri (fun _ : Unit => (0 : M4 A)) (fun _ _ => X) (RingHom.id A) 1 := by
  refine ⟨?_, fun _ => ⟨fun i j _ => by simp, fun i => by simp⟩⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨monic_one, by simp⟩`.
-/
example {A : Type} [CommRing A] (I : Ideal A) : Dist I 1 := ⟨monic_one, by simp⟩

/- English proof (translation)
Establish `a : ∀ Y : M4 C, adj (Y.map ψ) = (adj Y).map ψ` using `fun Y => by`. Use extensionality with `i j`. Simplify using `only [adj_apply, Matrix.map_apply, map_zsmul]`. Establish `e : ∀ g, adj (u.map ψ) * (M g).map (ψ.comp φ) * u.map ψ = (adj u * (M g).map φ * u).map ψ` using `fun g => by`. Rewrite using `[a, Matrix.map_mul, Matrix.map_mul]`.

Both sides reduce to the same expression. Use `⟨?_, fun g => ⟨fun i j hij => ?_, fun i => ?_⟩⟩` and prove the remaining obligations. Use `h.1` as an intermediate fact. Unfold `IsGSp at this ⊢`. Rewrite using `[a, ← Matrix.map_mul, this, one_smul, one_smul, Matrix.map_one _ (map_zero ψ) (map_one ψ)]`.

Rewrite using `[e, Matrix.map_apply, (h.2 g).1 i j hij, map_zero]`. Rewrite using `[e, Matrix.map_apply, ← hom_eval₂, (h.2 g).2 i, map_zero]`.
-/
theorem SpTri.map {ι A C C' : Type} [CommRing A] [CommRing C] [CommRing C'] {M : ι → M4 A} {P : ι → Fin 4 → A[X]}
    {φ : A →+* C} {u : M4 C} (h : SpTri M P φ u) (ψ : C →+* C') : SpTri M P (ψ.comp φ) (u.map ψ) := by
  have a : ∀ Y : M4 C, adj (Y.map ψ) = (adj Y).map ψ := fun Y => by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  have e : ∀ g, adj (u.map ψ) * (M g).map (ψ.comp φ) * u.map ψ = (adj u * (M g).map φ * u).map ψ := fun g => by
    rw [a, Matrix.map_mul, Matrix.map_mul]
    rfl
  refine ⟨?_, fun g => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have := h.1
    unfold IsGSp at this ⊢
    rw [a, ← Matrix.map_mul, this, one_smul, one_smul, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  · rw [e, Matrix.map_apply, (h.2 g).1 i j hij, map_zero]
  · rw [e, Matrix.map_apply, ← hom_eval₂, (h.2 g).2 i, map_zero]

/- English proof (translation)
Establish `a : ∀ Y : M4 C, adj (Y.map ψ) = (adj Y).map ψ` using `fun Y => by`. Use extensionality with `i j`. Simplify using `only [adj_apply, Matrix.map_apply, map_zsmul]`. Establish `e : ∀ g, adj (u.map ψ) * (M g).map (ψ.comp φ) * u.map ψ = (adj u * (M g).map φ * u).map ψ` using `fun g => by`. Rewrite using `[a, Matrix.map_mul, Matrix.map_mul]`.

Both sides reduce to the same expression. Use `⟨?_, fun g => ⟨fun i j hij => hψ ?_, fun i => hψ ?_⟩⟩` and prove the remaining obligations. Use `h.1` as an intermediate fact. Unfold `IsGSp at this ⊢`. Rewrite `this` using `[a, ← Matrix.map_mul, one_smul, ← Matrix.map_one ψ (map_zero ψ) (map_one ψ)]`.

Rewrite using `[one_smul]`. Conclude with `Matrix.map_injective hψ this`. Use `(h.2 g).1 i j hij` as an intermediate fact. Rewrite `this` using `[e, Matrix.map_apply, ← map_zero ψ]`. Then use the resulting hypothesis. Use `(h.2 g).2 i` as an intermediate fact.

Rewrite `this` using `[e, Matrix.map_apply, ← hom_eval₂, ← map_zero ψ]`. Then use the resulting hypothesis.
-/
theorem SpTri.of_map {ι A C C' : Type} [CommRing A] [CommRing C] [CommRing C'] {M : ι → M4 A} {P : ι → Fin 4 → A[X]}
    {φ : A →+* C} {u : M4 C} (ψ : C →+* C') (hψ : Function.Injective ψ) (h : SpTri M P (ψ.comp φ) (u.map ψ)) :
    SpTri M P φ u := by
  have a : ∀ Y : M4 C, adj (Y.map ψ) = (adj Y).map ψ := fun Y => by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  have e : ∀ g, adj (u.map ψ) * (M g).map (ψ.comp φ) * u.map ψ = (adj u * (M g).map φ * u).map ψ := fun g => by
    rw [a, Matrix.map_mul, Matrix.map_mul]
    rfl
  refine ⟨?_, fun g => ⟨fun i j hij => hψ ?_, fun i => hψ ?_⟩⟩
  · have := h.1
    unfold IsGSp at this ⊢
    rw [a, ← Matrix.map_mul, one_smul, ← Matrix.map_one ψ (map_zero ψ) (map_one ψ)] at this
    rw [one_smul]
    exact Matrix.map_injective hψ this
  · have := (h.2 g).1 i j hij
    rwa [e, Matrix.map_apply, ← map_zero ψ] at this
  · have := (h.2 g).2 i
    rwa [e, Matrix.map_apply, ← hom_eval₂, ← map_zero ψ] at this

end UpperTheory.V.Ws.Pp

end
