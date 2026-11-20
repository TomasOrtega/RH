import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.QuotAcycCut

def ProdAcyc : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] (n : ℕ) (R : Fin n → Type) [∀ k, CommRing (R k)],
  Nonempty (A ≃+* ∀ k, R k) → (∀ k, Acyc q (sp (R k))) → Acyc q (sp A)

def Hens : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c),
    (∀ j, ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
      (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (D.obj j ≃+* ∀ k, R k)) ∧
    IsUnit (q : c.pt) ∧ ∃ K : Ideal c.pt, HenselianRing c.pt K ∧ Nonempty (B ⧸ I ≃+* c.pt ⧸ K)

/- English proof (translation)
Introduce `H q B _ _ I hB hq`. Take `⟨J, _, _, D, c, hc, hD, hqc, K, hK, ⟨e⟩⟩` from `hH q B I hB hq`. Establish `hst : ∀ j, Acyc q (sp (D.obj j))`. Introduce `j`. Take `⟨m, R, _, hR, hiso⟩` from `hD j`.

Use `hP H q (D.obj j) m R hiso fun k => ?_` and prove the remaining obligations. Use `(hR k).1` as an intermediate fact. Conclude with `H.b5 q (R k) (hR k).2.1 (hR k).2.2`. Establish `hC : Acyc q (sp c.pt)`. Introduce `n i hn`.

Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ x : Ht q (sp c.pt) n i, x = 0`. Introduce `x`. Take `⟨j, y, rfl⟩` from `(H.b1 q D c hc n i).1 x hqc`. Use `hst j n i hn` as an intermediate fact.

Rewrite using `[Subsingleton.elim y 0, map_zero]`. Rewrite using `[h0 x, h0 y]`. Establish `hCK : Acyc q (sp (c.pt ⧸ K))`. Introduce `n i hn`. Use `hC n i hn` as an intermediate fact.

Establish `hE` using `H.e1 q c.pt K hqc i n`. Conclude with `hE.2.subsingleton`. Conclude with `hP H q (B ⧸ I) 1 (fun _ => c.pt ⧸ K) ⟨e.trans (RingEquiv.piUnique (fun _ : Fin 1 => c.pt ⧸ K)).symm⟩ fun _ => hCK`.
-/
theorem goal_of (hP : ProdAcyc) (hH : Hens) : LateralTheory.E.t_E2Cut.QuotAcyc := by
  intro H q B _ _ I hB hq
  obtain ⟨J, _, _, D, c, hc, hD, hqc, K, hK, ⟨e⟩⟩ := hH q B I hB hq

  have hst : ∀ j, Acyc q (sp (D.obj j)) := by
    intro j
    obtain ⟨m, R, _, hR, hiso⟩ := hD j
    refine hP H q (D.obj j) m R hiso fun k => ?_
    have := (hR k).1
    exact H.b5 q (R k) (hR k).2.1 (hR k).2.2

  have hC : Acyc q (sp c.pt) := by
    intro n i hn
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ x : Ht q (sp c.pt) n i, x = 0 := by
      intro x
      obtain ⟨j, y, rfl⟩ := (H.b1 q D c hc n i).1 x hqc
      have := hst j n i hn
      rw [Subsingleton.elim y 0, map_zero]
    rw [h0 x, h0 y]

  have hCK : Acyc q (sp (c.pt ⧸ K)) := by
    intro n i hn
    have := hC n i hn
    have hE := H.e1 q c.pt K hqc i n
    exact hE.2.subsingleton
  exact hP H q (B ⧸ I) 1 (fun _ => c.pt ⧸ K) ⟨e.trans (RingEquiv.piUnique (fun _ : Fin 1 => c.pt ⧸ K)).symm⟩ fun _ => hCK

end LateralTheory.E.QuotAcycCut
