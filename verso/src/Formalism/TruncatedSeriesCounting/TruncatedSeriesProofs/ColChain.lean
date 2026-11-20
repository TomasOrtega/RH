import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

section Chain

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

/- English proof (authored)
Use the maps Y/X → Z/X → Z/Y induced by inclusion and quotient. The inclusion is injective because a representative from Y becomes zero exactly when it lies in X. The quotient map is surjective because the same representative in Z can be used in either quotient. Its kernel consists of classes represented by elements of Y, precisely the image of the inclusion. Length additivity for this short exact sequence gives the equality.
-/
theorem chain_len_add (X Y Z : Submodule O M) (hXY : X ≤ Y) (hYZ : Y ≤ Z) :
    Module.length O (↥Z ⧸ X.comap Z.subtype) =
      Module.length O (↥Y ⧸ X.comap Y.subtype) + Module.length O (↥Z ⧸ Y.comap Z.subtype) := by
  have hle : X.comap Y.subtype ≤ (X.comap Z.subtype).comap (Submodule.inclusion hYZ) :=
    fun x hx => hx
  have hle2 : X.comap Z.subtype ≤ (Y.comap Z.subtype).comap LinearMap.id := fun x hx => hXY hx
  let f := Submodule.mapQ (X.comap Y.subtype) (X.comap Z.subtype) (Submodule.inclusion hYZ) hle
  let g := Submodule.mapQ (X.comap Z.subtype) (Y.comap Z.subtype) LinearMap.id hle2
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 ?_
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hq
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk z, by rw [Submodule.mapQ_apply, LinearMap.id_apply]⟩
  have hfg : Function.Exact f g := by
    intro q
    constructor
    · intro hz
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero] at hz
      have hz' : (z : M) ∈ Y := hz
      exact ⟨Submodule.Quotient.mk ⟨z, hz'⟩, by rw [Submodule.mapQ_apply]; rfl⟩
    · rintro ⟨q', rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero]
      exact y.2
  exact Module.length_eq_add_of_exact f g hf hg hfg

/- English proof (authored)
Use the map from A/(A∩X) to Z/(Z∩X) induced by inclusion. Given a representative z in Z, write z = a+x with a in A and x in X, using Z ≤ A+X. The class of z is the image of the class of a. The map is surjective, so the target has length at most the source.
-/
theorem chain_len_le_of_le_sup (A X Z : Submodule O M) (hAZ : A ≤ Z) (hZ : Z ≤ A ⊔ X) :
    Module.length O (↥Z ⧸ X.comap Z.subtype) ≤ Module.length O (↥A ⧸ X.comap A.subtype) := by
  have hle : X.comap A.subtype ≤ (X.comap Z.subtype).comap (Submodule.inclusion hAZ) :=
    fun x hx => hx
  apply Module.length_le_of_surjective (Submodule.mapQ _ _ (Submodule.inclusion hAZ) hle)
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.1 (hZ z.2)
  refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
  show (a - (z : M)) ∈ X
  rw [← hax, show a - (a + x) = -x by abel]
  exact X.neg_mem hx

/- English proof (authored)
The map A/(A∩P) → M/P sends the class of a to its class in M/P. Every m in M can be written as a+p by the assumption M = A+P, so this map is surjective. Apply the length inequality for a surjection.
-/
theorem chain_len_le_top (A P : Submodule O M) (hA : ⊤ ≤ A ⊔ P) :
    Module.length O (M ⧸ P) ≤ Module.length O (↥A ⧸ P.comap A.subtype) := by
  apply Module.length_le_of_surjective (Submodule.mapQ (P.comap A.subtype) P A.subtype le_rfl)
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha, x, hx, hax⟩ :=
    Submodule.mem_sup.1 (hA (Submodule.mem_top : m ∈ (⊤ : Submodule O M)))
  refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
  show (a - m) ∈ P
  rw [← hax, show a - (a + x) = -x by abel]
  exact P.neg_mem hx

end Chain

/- English proof (authored)
An element of A already lies in C by the inclusion A ≤ C. Membership in B∩C on restricting to A is therefore equivalent to membership in B, giving equality of the two restricted submodules.
-/
private lemma comap_subtype_inf_of_le {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (A B C : Submodule O M) (h : A ≤ C) : (B ⊓ C).comap A.subtype = B.comap A.subtype := by
  ext x
  simp [h x.2]

/- English proof (authored)
Induct on k. At k = 0 the sum is empty, and the terminal quotient represents the whole quotient since F₀ is the full module. For the induction step write U = Fₖ, V = Fₖ₊₁, X = P∩U, and Y = (V+P)∩U. Length additivity decomposes the old terminal term length(U/X) into length(Y/X) and length(U/Y). The latter is the new summand.

Since V ≤ U, the modular law gives Y = V+(P∩U). The map V/(V∩P) → Y/X is surjective by this equality, so length(Y/X) is bounded by the new terminal term. Substitute the two bounds into the induction hypothesis and append the new summand.
-/
theorem column_chain_bound : ColChain := by
  unfold ColChain
  intro O _ M _ _ P k F h0 hF
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    exact chain_len_le_top (F 0) P (by rw [h0]; exact le_sup_left)
  | succ k ih =>
    have hk : F (k + 1) ≤ F k := hF k (Nat.lt_succ_self k)
    have ih' := ih (fun i hi => hF i (Nat.lt_succ_of_lt hi))
    have e1 := chain_len_add (P ⊓ F k) ((F (k + 1) ⊔ P) ⊓ F k) (F k)
      (inf_le_inf_right _ le_sup_right) inf_le_right
    rw [comap_subtype_inf_of_le (F k) P (F k) le_rfl, comap_subtype_inf_of_le (F k) (F (k + 1) ⊔ P) (F k) le_rfl] at e1
    have e2 := chain_len_le_of_le_sup (F (k + 1)) (P ⊓ F k) ((F (k + 1) ⊔ P) ⊓ F k)
      (le_inf le_sup_left hk) (le_of_eq (sup_inf_assoc_of_le P hk))
    rw [comap_subtype_inf_of_le (F (k + 1)) P (F k) hk] at e2
    rw [Finset.sum_range_succ, add_assoc]
    refine le_trans ih' (add_le_add le_rfl ?_)
    rw [e1, add_comm]
    exact add_le_add le_rfl e2

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
