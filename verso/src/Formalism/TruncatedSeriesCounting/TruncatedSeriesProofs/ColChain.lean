import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

section Chain

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

/- English proof (translation)
Establish `hle : X.comap Y.subtype ≤ (X.comap Z.subtype).comap (Submodule.inclusion hYZ)` using `fun x hx => hx`. Establish `hle2 : X.comap Z.subtype ≤ (Y.comap Z.subtype).comap LinearMap.id` using `fun x hx => hXY hx`. Set `f` to `Submodule.mapQ (X.comap Y.subtype) (X.comap Z.subtype) (Submodule.inclusion hYZ) hle`. Set `g` to `Submodule.mapQ (X.comap Z.subtype) (Y.comap Z.subtype) LinearMap.id hle2`. Establish `hf : Function.Injective f`.

Use `(injective_iff_map_eq_zero f).2 ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Rewrite `hq` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Conclude with `hq`. Establish `hg : Function.Surjective g`. Introduce `q`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Conclude with `⟨Submodule.Quotient.mk z, by rw [Submodule.mapQ_apply, LinearMap.id_apply]⟩`.

Establish `hfg : Function.Exact f g`. Introduce `q`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Rewrite `hz` using `[Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]`. Establish `hz' : (z : M) ∈ Y` using `hz`. Conclude with `⟨Submodule.Quotient.mk ⟨z, hz'⟩, by rw [Submodule.mapQ_apply]; rfl⟩`. Introduce and unpack `⟨q', rfl⟩`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ q'`.

Rewrite using `[Submodule.mapQ_apply, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `y.2`. Conclude with `Module.length_eq_add_of_exact f g hf hg hfg`.
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

/- English proof (translation)
Establish `hle : X.comap A.subtype ≤ (X.comap Z.subtype).comap (Submodule.inclusion hAZ)` using `fun x hx => hx`. Apply `Module.length_le_of_surjective (Submodule.mapQ _ _ (Submodule.inclusion hAZ) hle)` to reduce the goal to its premises. Introduce `q`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨a, ha, x, hx, hax⟩` from `Submodule.mem_sup.1 (hZ z.2)`.

Use `⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mapQ_apply, Submodule.Quotient.eq]`. Use `show (a - (z : M)) ∈ X`. Rewrite using `[← hax, show a - (a + x) = -x by abel]`. Conclude with `X.neg_mem hx`.
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

/- English proof (translation)
Apply `Module.length_le_of_surjective (Submodule.mapQ (P.comap A.subtype) P A.subtype le_rfl)` to reduce the goal to its premises. Introduce `q`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨a, ha, x, hx, hax⟩` from `Submodule.mem_sup.1 (hA (Submodule.mem_top : m ∈ (⊤ : Submodule O M)))`. Use `⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.mapQ_apply, Submodule.Quotient.eq]`. Use `show (a - m) ∈ P`. Rewrite using `[← hax, show a - (a + x) = -x by abel]`. Conclude with `P.neg_mem hx`.
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

/- English proof (translation)
Use extensionality with `x`. Simplify using `[h x.2]`.
-/
private lemma comap_subtype_inf_of_le {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (A B C : Submodule O M) (h : A ≤ C) : (B ⊓ C).comap A.subtype = B.comap A.subtype := by
  ext x
  simp [h x.2]

/- English proof (translation)
Unfold `ColChain`. Introduce `O _ M _ _ P k F h0 hF`. Proceed by induction on `k with`. Consider the case `zero`. Simplify using `only [Finset.range_zero, Finset.sum_empty, zero_add]`.

Conclude with `chain_len_le_top (F 0) P (by rw [h0]; exact le_sup_left)`. Consider the case `succ k ih`. Establish `hk : F (k + 1) ≤ F k` using `hF k (Nat.lt_succ_self k)`. Establish `ih'` using `ih (fun i hi => hF i (Nat.lt_succ_of_lt hi))`. Establish `e1` using `chain_len_add (P ⊓ F k) ((F (k + 1) ⊔ P) ⊓ F k) (F k) (inf_le_inf_right _ le_sup_right) inf_le_right`.

Rewrite `e1` using `[comap_subtype_inf_of_le (F k) P (F k) le_rfl, comap_subtype_inf_of_le (F k) (F (k + 1) ⊔ P) (F k) le_rfl]`. Establish `e2` using `chain_len_le_of_le_sup (F (k + 1)) (P ⊓ F k) ((F (k + 1) ⊔ P) ⊓ F k) (le_inf le_sup_left hk) (le_of_eq (sup_inf_assoc_of_le P hk))`. Rewrite `e2` using `[comap_subtype_inf_of_le (F (k + 1)) P (F k) hk]`. Rewrite using `[Finset.sum_range_succ, add_assoc]`. Use `le_trans ih' (add_le_add le_rfl ?_)` and prove the remaining obligations.

Rewrite using `[e1, add_comm]`. Conclude with `add_le_add le_rfl e2`.
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
