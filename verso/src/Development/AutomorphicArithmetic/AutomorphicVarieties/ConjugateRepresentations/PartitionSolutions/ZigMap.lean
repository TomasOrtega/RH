import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

/- English proof (translation)
Introduce `Γ V S _ _ _ d G P hd' hi ha q`. Proceed by induction on `q with`. Consider the case `zero`. Introduce `k u c h x hx`. Use `show P 0 (u x) = G.incl (c x)`.

Rewrite using `[h x hx, hi]`. Consider the case `succ q ih`. Introduce and unpack `k u c ⟨b, hb, hdb, hz⟩`. Use `⟨fun x => P q (b x), fun γ x hx => ?_, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Use `show P q (b (x.map (γ * ·))) = G.act q γ (P q (b x))`.

Rewrite using `[hb γ x hx, ha]`. Use `show G.dOm q (P q (b x)) = P (q + 1) (u x)`. Rewrite using `[hd', hdb x hx]`. Establish `e : hd (fun x => P q (b x)) = fun x => P q (hd b x)`. Use function extensionality and compare the values at `fun x => hdFacts.2.2.2.1 Γ _ _ (P q).toAddMonoidHom b x`.

Rewrite using `[e]`. Conclude with `ih (k + 1) (hd b) c hz`.
-/
theorem UpperTheory.V.Cj.A.zigMap :
    ZigMap := by
  intro Γ V S _ _ _ d G P hd' hi ha q
  induction q with
  | zero =>
    intro k u c h x hx
    show P 0 (u x) = G.incl (c x)
    rw [h x hx, hi]
  | succ q ih =>
    rintro k u c ⟨b, hb, hdb, hz⟩
    refine ⟨fun x => P q (b x), fun γ x hx => ?_, fun x hx => ?_, ?_⟩
    · show P q (b (x.map (γ * ·))) = G.act q γ (P q (b x))
      rw [hb γ x hx, ha]
    · show G.dOm q (P q (b x)) = P (q + 1) (u x)
      rw [hd', hdb x hx]
    · have e : hd (fun x => P q (b x)) = fun x => P q (hd b x) :=
        funext fun x => hdFacts.2.2.2.1 Γ _ _ (P q).toAddMonoidHom b x
      rw [e]
      exact ih (k + 1) (hd b) c hz
