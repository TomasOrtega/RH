import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.EtSpreadsOf

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.SpreadPf.Lift

variable {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}

/- English proof (translation)
Establish `hc'` using `isColimitOfPreserves (forget CommRingCat.{0}) hc`. Take `⟨j, x, hx⟩` from `Types.jointly_surjective_of_isColimit hc' a`. Conclude with `⟨j, x, hx⟩`.
-/
theorem lift_elem (hc : IsColimit c) (a : c.pt) : ∃ (j : J) (x : D.obj j), c.ι.app j x = a := by
  have hc' := isColimitOfPreserves (forget CommRingCat.{0}) hc
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hc' a
  exact ⟨j, x, hx⟩

/- English proof (translation)
Rewrite using `[MvPolynomial.map_map, ← CommRingCat.hom_comp, c.w]`.
-/
theorem map_ι_map {σ : Type} {j k : J} (u : j ⟶ k) (q : MvPolynomial σ (D.obj j)) :
    MvPolynomial.map (c.ι.app k).hom (MvPolynomial.map (D.map u).hom q) = MvPolynomial.map (c.ι.app j).hom q := by
  rw [MvPolynomial.map_map, ← CommRingCat.hom_comp, c.w]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Take `⟨j, x, hx⟩` from `lift_elem hc a`. Conclude with `⟨j, MvPolynomial.C x, by simp [hx]⟩`. Consider the case `add p q hp hq`.

Take `⟨j₁, q₁, h₁⟩` from `hp`. Take `⟨j₂, q₂, h₂⟩` from `hq`. Use `⟨IsFiltered.max j₁ j₂, MvPolynomial.map (D.map (IsFiltered.leftToMax j₁ j₂)).hom q₁ + MvPolynomial.map (D.map (IsFiltered.rightToMax j₁ j₂)).hom q₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_ι_map, map_ι_map, h₁, h₂]`. Consider the case `mul_X p i hp`.

Take `⟨j, q, h⟩` from `hp`. Conclude with `⟨j, q * MvPolynomial.X i, by simp [h]⟩`.
-/
theorem lift_poly (hc : IsColimit c) {σ : Type} (p : MvPolynomial σ c.pt) :
    ∃ (j : J) (q : MvPolynomial σ (D.obj j)), MvPolynomial.map (c.ι.app j).hom q = p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨j, x, hx⟩ := lift_elem hc a
    exact ⟨j, MvPolynomial.C x, by simp [hx]⟩
  | add p q hp hq =>
    obtain ⟨j₁, q₁, h₁⟩ := hp
    obtain ⟨j₂, q₂, h₂⟩ := hq
    refine ⟨IsFiltered.max j₁ j₂, MvPolynomial.map (D.map (IsFiltered.leftToMax j₁ j₂)).hom q₁ +
      MvPolynomial.map (D.map (IsFiltered.rightToMax j₁ j₂)).hom q₂, ?_⟩
    rw [map_add, map_ι_map, map_ι_map, h₁, h₂]
  | mul_X p i hp =>
    obtain ⟨j, q, h⟩ := hp
    exact ⟨j, q * MvPolynomial.X i, by simp [h]⟩

/- English proof (translation)
The claim follows from `| 0, _ => ⟨IsFiltered.nonempty.some, fun i => i.elim0, fun i => i.elim0⟩ | m + 1, p => by obtain ⟨j₁, q₁, h₁⟩ := lift_polys hc m (fun i => p i.succ) obtain ⟨j₂, q₂, h₂⟩ := lift_poly hc (p 0) refine ⟨IsFiltered.max j₁ j₂, Fin.cons (MvPolynomial.map (D.map (IsFiltered.rightToMax j₁ …`.
-/
theorem lift_polys (hc : IsColimit c) {σ : Type} : ∀ (m : ℕ) (p : Fin m → MvPolynomial σ c.pt),
    ∃ (j : J) (q : Fin m → MvPolynomial σ (D.obj j)), ∀ i, MvPolynomial.map (c.ι.app j).hom (q i) = p i
  | 0, _ => ⟨IsFiltered.nonempty.some, fun i => i.elim0, fun i => i.elim0⟩
  | m + 1, p => by
    obtain ⟨j₁, q₁, h₁⟩ := lift_polys hc m (fun i => p i.succ)
    obtain ⟨j₂, q₂, h₂⟩ := lift_poly hc (p 0)
    refine ⟨IsFiltered.max j₁ j₂, Fin.cons (MvPolynomial.map (D.map (IsFiltered.rightToMax j₁ j₂)).hom q₂)
      (fun i => MvPolynomial.map (D.map (IsFiltered.leftToMax j₁ j₂)).hom (q₁ i)), ?_⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]; rw [map_ι_map, h₂]
    · simp only [Fin.cons_succ]; rw [map_ι_map, h₁]

end LateralTheory.E.SpreadPf.Lift
