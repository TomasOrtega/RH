import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

open UpperTheory.V.Af UpperTheory.V.Af.CohB GlobalTheory.CuspRep in
/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Use `haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
private theorem relIndex_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Rewrite using `[Subgroup.relIndex_comap]`. Introduce `h0`. Conclude with `h (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le f K) h0)`.
-/
private theorem comm_comap {G H : Type} [Group G] [Group H] (f : H →* G) (U K : Subgroup G)
    (h : U.relIndex K ≠ 0) : (U.comap f).relIndex (K.comap f) ≠ 0 := by
  rw [Subgroup.relIndex_comap]
  intro h0
  exact h (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le f K) h0)

/- English proof (translation)
Introduce `F _ _ n Γ hΓ g U hUo hUc`. Use `set U' := U.comap (MulAut.conj g⁻¹).toMonoidHom with hU'`. Establish `hc : Continuous (fun x : GL (Fin n) (GlobalTheory.CuspRep.Af F) => g⁻¹ * x * g)` using `by fun_prop`. Establish `hc' : Continuous (fun x : GL (Fin n) (GlobalTheory.CuspRep.Af F) => g * x * g⁻¹)` using `by fun_prop`. Establish `e1 : (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) = (fun x => g⁻¹ * x * g) ⁻¹' U`.

Use extensionality with `x`. Simplify using `[hU']`. Establish `e2 : (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) = (fun x => g * x * g⁻¹) '' U`. Rewrite using `[e1]`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨_, hx, by simp [mul_assoc]⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify `hy` using `[mul_assoc]`.

Establish `ho : IsOpen (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F)))` using `e1 ▸ hUo.preimage hc`. Establish `hk : IsCompact (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F)))` using `e2 ▸ hUc.image hc'`. Establish `h1` using `comm_comap (UpperTheory.V.Af.CohB.ratAf F n) _ _ (relIndex_open_compact U' _ ho (UpperTheory.V.Af.isCompact_KLev (F := F) (n := n) le_rfl))`. Establish `h2` using `comm_comap (UpperTheory.V.Af.CohB.ratAf F n) _ _ (relIndex_open_compact _ U' (UpperTheory.V.Af.isOpen_KLev (F := F) (n := n) le_rfl) hk)`. Establish `h3 : Γ.relIndex ((UpperTheory.V.Af.KLev F n 1).comap (UpperTheory.V.Af.CohB.ratAf F n)) ≠ 0` using `fun h0 => hΓ.index_ne_zero (by`.

Rewrite using `[← Subgroup.relIndex_top_right]`. Conclude with `Subgroup.relIndex_eq_zero_of_le_right le_top h0)`. Establish `h4` using `Subgroup.relIndex_inf_ne_zero h3 h1`. Establish `h5 : ((UpperTheory.V.Af.KLev F n 1).comap (UpperTheory.V.Af.CohB.ratAf F n)).relIndex (Γ ⊓ UpperTheory.V.Af.CohB.arith g U) ≠ 0` using `fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)`. Use `first`.

Consider the case `exact ⟨h4, h5⟩`. Consider the case `exact ⟨⟨h4⟩, ⟨h5⟩⟩`.
-/
theorem UpperTheory.arithmetic_subgroups_commensurable :
    UpperTheory.V.Af.CohB.ArithComm := by
  intro F _ _ n Γ hΓ g U hUo hUc
  set U' := U.comap (MulAut.conj g⁻¹).toMonoidHom with hU'
  have hc : Continuous (fun x : GL (Fin n) (GlobalTheory.CuspRep.Af F) => g⁻¹ * x * g) := by fun_prop
  have hc' : Continuous (fun x : GL (Fin n) (GlobalTheory.CuspRep.Af F) => g * x * g⁻¹) := by fun_prop
  have e1 : (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) = (fun x => g⁻¹ * x * g) ⁻¹' U := by
    ext x; simp [hU']
  have e2 : (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) = (fun x => g * x * g⁻¹) '' U := by
    rw [e1]
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
  have ho : IsOpen (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) := e1 ▸ hUo.preimage hc
  have hk : IsCompact (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) := e2 ▸ hUc.image hc'
  have h1 := comm_comap (UpperTheory.V.Af.CohB.ratAf F n) _ _
    (relIndex_open_compact U' _ ho (UpperTheory.V.Af.isCompact_KLev (F := F) (n := n) le_rfl))
  have h2 := comm_comap (UpperTheory.V.Af.CohB.ratAf F n) _ _
    (relIndex_open_compact _ U' (UpperTheory.V.Af.isOpen_KLev (F := F) (n := n) le_rfl) hk)
  have h3 : Γ.relIndex ((UpperTheory.V.Af.KLev F n 1).comap (UpperTheory.V.Af.CohB.ratAf F n)) ≠ 0 := fun h0 =>
    hΓ.index_ne_zero (by
      rw [← Subgroup.relIndex_top_right]
      exact Subgroup.relIndex_eq_zero_of_le_right le_top h0)
  have h4 := Subgroup.relIndex_inf_ne_zero h3 h1
  have h5 : ((UpperTheory.V.Af.KLev F n 1).comap (UpperTheory.V.Af.CohB.ratAf F n)).relIndex (Γ ⊓ UpperTheory.V.Af.CohB.arith g U) ≠ 0 :=
    fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  first
    | exact ⟨h4, h5⟩
    | exact ⟨⟨h4⟩, ⟨h5⟩⟩
