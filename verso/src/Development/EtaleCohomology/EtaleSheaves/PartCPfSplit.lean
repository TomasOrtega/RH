import Development.EtaleCohomology.EtaleSheaves.PartCPf

noncomputable section
open Polynomial LateralTheory.E.PartDiagCut GlobalTheory.EtC

namespace LateralTheory.E.PartCPfSplit

/- English proof (translation)
Introduce `B _ _ I hB P p hm`. Establish `key : ∀ e : P.1, ∃ g : Fin p.natDegree → Localization (S I e.1), p.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) = ∏ l, (X - C (g l))`. Introduce `e`. Establish `h0 : (0:B) ∉ S I e.1`. Introduce and unpack `⟨t, ht⟩`.

Apply `(P.idem e.1 e.2).2` to reduce the goal to its premises. Simplify using `using ht.symm`. Take `⟨hdom, haic⟩` from `hLoc B (S I e.1) h0 hB`. Establish `hme` using `hm.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)`. Take `⟨s, hs⟩` from `hMS _ haic _ hme`.

Establish `hcard : s.toList.length = p.natDegree`. Use `congrArg natDegree hs` as an intermediate fact. Rewrite `this` using `[natDegree_multiset_prod_X_sub_C_eq_card, hm.natDegree_map]`. Simplify using `[this]`. Use `⟨fun l => s.toList.get (Fin.cast hcard.symm l), ?_⟩` and prove the remaining obligations.

Rewrite using `[hs]`. Use `conv_lhs => rw [← Multiset.coe_toList s]`. Rewrite using `[Multiset.map_coe, Multiset.prod_coe]`. Rewrite using `[← Fintype.prod_equiv (finCongr hcard) (fun i : Fin s.toList.length => X - C (s.toList.get i)) _ (fun _ => rfl)]`. Rewrite using `[← List.prod_ofFn]`.

Use `congr 1`. Apply the tactic sequence `apply List.ext_get <;> simp`. Use `choose g hg using key`. Use `⟨p.natDegree, fun l e => g e l, ?_⟩` and prove the remaining obligations. Use `Polynomial.ext fun k => funext fun e => ?_` and prove the remaining obligations.

Establish `h2 : (∏ l, (X - C (fun e => g e l))).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) = ∏ l, (X - C (g e l))` using `by simp [Polynomial.map_prod]`. Use `congrArg (coeff · k) ((hg e).trans h2.symm)` as an intermediate fact. Simplify `this` using `[coeff_map]`.
-/
theorem split_of (hLoc : LateralTheory.E.HensCut.LocAIC) (hMS : LateralTheory.E.HensCut.MonicSplits) : LateralTheory.E.PartCPf.Split := by
  intro B _ _ I hB P p hm
  have key : ∀ e : P.1, ∃ g : Fin p.natDegree → Localization (S I e.1),
      p.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) = ∏ l, (X - C (g l)) := by
    intro e
    have h0 : (0:B) ∉ S I e.1 := by
      rintro ⟨t, ht⟩
      apply (P.idem e.1 e.2).2
      simpa using ht.symm
    obtain ⟨hdom, haic⟩ := hLoc B (S I e.1) h0 hB
    have hme := hm.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)
    obtain ⟨s, hs⟩ := hMS _ haic _ hme
    have hcard : s.toList.length = p.natDegree := by
      have := congrArg natDegree hs
      rw [natDegree_multiset_prod_X_sub_C_eq_card, hm.natDegree_map] at this
      simp [this]
    refine ⟨fun l => s.toList.get (Fin.cast hcard.symm l), ?_⟩
    rw [hs]
    conv_lhs => rw [← Multiset.coe_toList s]
    rw [Multiset.map_coe, Multiset.prod_coe]
    rw [← Fintype.prod_equiv (finCongr hcard) (fun i : Fin s.toList.length => X - C (s.toList.get i)) _ (fun _ => rfl)]
    rw [← List.prod_ofFn]
    congr 1
    apply List.ext_get <;> simp
  choose g hg using key
  refine ⟨p.natDegree, fun l e => g e l, ?_⟩
  refine Polynomial.ext fun k => funext fun e => ?_
  have h2 : (∏ l, (X - C (fun e => g e l))).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)
      = ∏ l, (X - C (g e l)) := by simp [Polynomial.map_prod]
  have := congrArg (coeff · k) ((hg e).trans h2.symm)
  simpa [coeff_map] using this

/- English proof (translation)
The claim follows from `LateralTheory.E.PartCPf.PartC_of' (split_of hLoc hMS) hIP hA hl`.
-/
theorem PartC_of (hLoc : LateralTheory.E.HensCut.LocAIC) (hMS : LateralTheory.E.HensCut.MonicSplits) (hIP : LateralTheory.E.HensCut.IdemPart)
    (hA : LateralTheory.E.PartDiagCut.PartA) (hl : LateralTheory.E.PartCPf.Lift) : LateralTheory.E.PartDiagCut.PartC :=
  LateralTheory.E.PartCPf.PartC_of' (split_of hLoc hMS) hIP hA hl

end LateralTheory.E.PartCPfSplit
