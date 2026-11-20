import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
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
