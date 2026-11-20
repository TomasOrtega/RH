import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons p L ih`. Establish `h1 : p.1 = 1` using `hL p (by simp)`. Establish `hpos : 0 < q - 1` using `by omega`.

Rewrite using `[List.map_cons, List.sum_cons, ih (fun r hr => hL r (List.mem_cons_of_mem _ hr)), List.map_cons, h1]`. Simplify using `[Nat.div_self hpos]`.
-/
private theorem polTop_sum (q : ℕ) (hq : 2 ≤ q) (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, p.1 = 1) :
    (L.map fun p => (Multiset.range p.1).map fun j =>
      ((1 : ℕ), ((p.2 * q ^ j * ((q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (q - 1)))).sum =
      ((L.map fun p => (p.1, ((p.2 : ℕ) : ZMod (q - 1))) : List _) : Multiset _) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have h1 : p.1 = 1 := hL p (by simp)
    have hpos : 0 < q - 1 := by omega
    rw [List.map_cons, List.sum_cons, ih (fun r hr => hL r (List.mem_cons_of_mem _ hr)), List.map_cons,
      h1]
    simp [Nat.div_self hpos]

/- English proof (translation)
Introduce `b x hq hL hx`. Establish `hpos : 0 < b.q - 1` using `by omega`. Establish `hb : b.blocks b.q = ((b.D ++ b.L).map fun p => (p.1, ((p.2 : ℕ) : ZMod (b.q - 1))) : List _)`. Unfold `Lbl.blocks`. Rewrite using `[polTop_sum b.q hq b.L hL, List.map_append, ← Multiset.coe_add]`.

Simplify using `[Nat.div_self hpos]`. Use `⟨hb, ?_⟩` and prove the remaining obligations. Unfold `Lbl.pol`. Rewrite using `[hb, Multiset.map_coe, Multiset.prod_coe, List.map_map]`. Use `congr 1`.

Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `p _`. Simplify using `only [Function.comp]`. Rewrite using `[ZMod.val_natCast, ← pow_eq_pow_mod p.2 hx]`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.polTop :
    PolTop := by
  intro b x hq hL hx
  have hpos : 0 < b.q - 1 := by omega
  have hb : b.blocks b.q = ((b.D ++ b.L).map fun p => (p.1, ((p.2 : ℕ) : ZMod (b.q - 1))) : List _) := by
    unfold Lbl.blocks
    rw [polTop_sum b.q hq b.L hL, List.map_append, ← Multiset.coe_add]
    simp [Nat.div_self hpos]
  refine ⟨hb, ?_⟩
  unfold Lbl.pol
  rw [hb, Multiset.map_coe, Multiset.prod_coe, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  rw [ZMod.val_natCast, ← pow_eq_pow_mod p.2 hx]
