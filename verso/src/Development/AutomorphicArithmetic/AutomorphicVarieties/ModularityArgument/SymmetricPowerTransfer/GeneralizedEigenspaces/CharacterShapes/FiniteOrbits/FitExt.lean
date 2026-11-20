import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Consider the cases of `V`. Consider the cases of `V'`. Consider the cases of `hc`. Consider the cases of `hH`. Both sides reduce to the same expression.
-/
private theorem lev_ext' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {V V' : Sig.Lev k} (hc : V.c = V'.c) (hH : V.H = V'.H) : V = V' := by
  cases V
  cases V'
  cases hc
  cases hH
  rfl

/- English proof (translation)
Introduce `L _ _ _ B T S₀ S V₀ VL A₀ A h₀ h hS hV hI`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Take `⟨w, hw, rfl⟩` from `(h₀.sg v).1 hv`. Conclude with `(h.sg _).2 ⟨w, hS hw, rfl⟩`.

Introduce `v hv`. Take `⟨w, hw, rfl⟩` from `(h₀.sg v).1 hv`. Establish `hs : IsSplitAt w` using `h₀.pl.split w (Finset.mem_coe.2 hw)`. Rewrite using `[h.s w (hS hw) hs, h₀.s w hw hs]`. Introduce `v hv`.

Take `⟨w, hw, rfl⟩` from `(h₀.sg v).1 hv`. Establish `hs : IsSplitAt w` using `h₀.pl.split w (Finset.mem_coe.2 hw)`. Establish `e : A.V (un w) = A₀.V (un w)` using `lev_ext' (by rw [h.c w (hS hw), h₀.c w hw, hV w hw]) (by`. Use extensionality with `x`. Rewrite using `[← h.H w (hS hw) hs x, ← h₀.H w hw hs x, hV w hw])`.

Rewrite using `[e]`. Introduce `v hv hn`. Take `⟨w, hw, rfl⟩` from `(h.sg v).1 hv`. Establish `hw0 : w ∉ S₀` using `fun hw0 => hn ((h₀.sg _).2 ⟨w, hw0, rfl⟩)`. Establish `hs : IsSplitAt w` using `h.pl.split w (Finset.mem_coe.2 hw)`.

Establish `hi` using `hI w hw hw0`. Establish `e : A.V (un w) = Sig.Lev.iw _` using `lev_ext' (by rw [h.c w hw, hi]; rfl) (by`. Use extensionality with `x`. Rewrite using `[← h.H w hw hs x, hi]`. Conclude with `(T w hs).Uo x)`.

Rewrite using `[e]`.
-/
theorem UpperTheory.V.Z.Sym.So.fitExt :
    UpperTheory.V.Z.Sym.So.FitExt := by
  intro L _ _ _ B T S₀ S V₀ VL A₀ A h₀ h hS hV hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    exact (h.sg _).2 ⟨w, hS hw, rfl⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    have hs : IsSplitAt w := h₀.pl.split w (Finset.mem_coe.2 hw)
    rw [h.s w (hS hw) hs, h₀.s w hw hs]
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    have hs : IsSplitAt w := h₀.pl.split w (Finset.mem_coe.2 hw)
    have e : A.V (un w) = A₀.V (un w) :=
      lev_ext' (by rw [h.c w (hS hw), h₀.c w hw, hV w hw]) (by
        ext x
        rw [← h.H w (hS hw) hs x, ← h₀.H w hw hs x, hV w hw])
    rw [e]
  · intro v hv hn
    obtain ⟨w, hw, rfl⟩ := (h.sg v).1 hv
    have hw0 : w ∉ S₀ := fun hw0 => hn ((h₀.sg _).2 ⟨w, hw0, rfl⟩)
    have hs : IsSplitAt w := h.pl.split w (Finset.mem_coe.2 hw)
    have hi := hI w hw hw0
    have e : A.V (un w) = Sig.Lev.iw _ :=
      lev_ext' (by rw [h.c w hw, hi]; rfl) (by
        ext x
        rw [← h.H w hw hs x, hi]
        exact (T w hs).Uo x)
    rw [e]

end
