import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointCutToFibreUnionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOpenNhdOneOfIntegralEqOneOnFinsetStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixLev
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `hx' : cInf x = 1` using `hx`. Establish `hy' : cInf y = 1` using `hy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `ga_ext` to reduce the goal to its premises. Conclude with `hx'.trans hy'.symm`.

Conclude with `Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => by`. Use `congrArg (fun z : GLw n v => (z : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j) (h v)` as an intermediate fact. Conclude with `this)`.
-/
theorem ext_fin {x y : UA E n} (hx : x ∈ finU E n) (hy : y ∈ finU E n) (h : ∀ v : Pl E, cLoc v x = cLoc v y) : x = y := by
  have hx' : cInf x = 1 := hx
  have hy' : cInf y = 1 := hy
  apply Subtype.ext
  apply ga_ext
  · exact hx'.trans hy'.symm
  · exact Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v =>
      by
        have := congrArg (fun z : GLw n v => (z : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j) (h v)
        exact this)

/- English proof (translation)
Establish `h1 : ∀ x : Af E, ∀ᶠ v in cofinite, pLoc E v x ∈ v.adicCompletionIntegers E` using `fun x => x.2`. Establish `h2 : ∀ i j : Fin n, ∀ᶠ v in cofinite, (cLoc v g) i j ∈ v.adicCompletionIntegers E ∧ (cLoc v g)⁻¹ i j ∈ v.adicCompletionIntegers E`. Introduce `i j`. Use `filter_upwards [h1 (pFin E ((g : GA E n) i j)), h1 (pFin E (((g⁻¹ : UA E n) : GA E n) i j))] with v hv hv'`. Use `⟨hv, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_inv]`. Conclude with `hv'`. Conclude with `Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h2 i)`.
-/
theorem integral_eventually (g : UA E n) : ∀ᶠ v in cofinite, ∀ i j : Fin n,
    (cLoc v g) i j ∈ v.adicCompletionIntegers E ∧ (cLoc v g)⁻¹ i j ∈ v.adicCompletionIntegers E := by
  have h1 : ∀ x : Af E, ∀ᶠ v in cofinite, pLoc E v x ∈ v.adicCompletionIntegers E := fun x => x.2
  have h2 : ∀ i j : Fin n, ∀ᶠ v in cofinite,
      (cLoc v g) i j ∈ v.adicCompletionIntegers E ∧ (cLoc v g)⁻¹ i j ∈ v.adicCompletionIntegers E := by
    intro i j
    filter_upwards [h1 (pFin E ((g : GA E n) i j)), h1 (pFin E (((g⁻¹ : UA E n) : GA E n) i j))] with v hv hv'
    refine ⟨hv, ?_⟩
    rw [← map_inv]
    exact hv'
  exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h2 i)

def fib (B : Finset (Pl E)) : Set (Pl E) :=
  {u | ∃ t ∈ B, u.under (𝓞 (maximalRealSubfield E)) = t.under (𝓞 (maximalRealSubfield E))}

/- English proof (translation)
Take `⟨t, ht, e⟩` from `hu`. Conclude with `⟨t, ht, h.symm.trans e⟩`.
-/
theorem fib_closed (B : Finset (Pl E)) (u v : Pl E)
    (h : u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E))) (hu : u ∈ fib B) : v ∈ fib B := by
  obtain ⟨t, ht, e⟩ := hu
  exact ⟨t, ht, h.symm.trans e⟩

def stabU (φ : UA E n → ℂ) : Subgroup (UA E n) where
  carrier := {x | RU E n x φ = φ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j ∈ _`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem one_entry_mem (v : Pl E) (i j : Fin n) : (1 : GLw n v) i j ∈ v.adicCompletionIntegers E := by
  change (1 : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j ∈ _
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/- English proof (translation)
Proceed by induction on `B using Finset.induction_on with`. Consider the case `empty`. Introduce `h hfin _ h1`. Establish `: h = 1` using `ext_fin hfin (one_mem _) fun v => by`. Rewrite using `[h1 v (by rintro ⟨t, ht, _⟩; simp at ht), map_one]`.

Rewrite using `[this]`. Conclude with `one_mem _`. Consider the case `insert t B _ ih`. Introduce `h hfin hK h1`. Take `⟨wt, ⟨hwtS, hwt⟩, _⟩` from `hS t`.

Take `⟨x, hxfin, hx⟩` from `GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion E n (fib {t}) (fib_closed {t}) h hfin`. Establish `hxloc : x ∈ locU n wt`. Use `Subgroup.mem_inf.2 ⟨hxfin, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker, hx u, if_neg]`. Introduce and unpack `⟨t', ht', e⟩`.

Rewrite `ht'` using `[Finset.mem_singleton]`. Substitute `ht'` using the available equality. Conclude with `hu (e.trans hwt.symm)`. Establish `hwtf : wt ∈ fib {t}` using `⟨t, Finset.mem_singleton_self t, hwt⟩`. Establish `hxS : x ∈ stabU φ`.

Take `⟨k, hk, hkx⟩` from `hK wt hwtS`. Use `hφ wt hwtS x hxloc ⟨k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[hx wt, if_pos hwtf, hkx]`. Establish `hrest : x⁻¹ * h ∈ stabU φ`. Use `ih _ (mul_mem (inv_mem hxfin) hfin) ?_ ?_` and prove the remaining obligations.

Introduce `w hw`. Rewrite using `[map_mul, map_inv, hx w]`. Use `split_ifs`. Conclude with `⟨1, one_mem _, by rw [inv_mul_cancel]; rfl⟩`. Rewrite using `[inv_one, one_mul]`.

Conclude with `hK w hw`. Introduce `v hv`. Rewrite using `[map_mul, map_inv, hx v]`. Use `split_ifs with hvt`. Conclude with `inv_mul_cancel _`.

Rewrite using `[inv_one, one_mul]`. Use `h1 v ?_` and prove the remaining obligations. Introduce and unpack `⟨t', ht', e⟩`. Break down `Finset.mem_insert.1 ht' with rfl | ht'` into its components or cases. Conclude with `hvt ⟨t', Finset.mem_singleton_self _, e⟩`.

Conclude with `hv ⟨t', ht', e⟩`. Establish `: h = x * (x⁻¹ * h)` using `by group`. Rewrite using `[this]`. Conclude with `mul_mem hxS hrest`.
-/
theorem local_fixed (S : Set (Pl E)) (hS : IsSection S) (K' : ∀ w : Pl E, Subgroup (UL n w)) (φ : UA E n → ℂ)
    (hφ : ∀ w ∈ S, ∀ x ∈ locU n w, (∃ k ∈ K' w, k.1 = cLoc w x) → RU E n x φ = φ) (B : Finset (Pl E)) :
    ∀ h : UA E n, h ∈ finU E n → (∀ w ∈ S, ∃ k ∈ K' w, k.1 = cLoc w h) → (∀ v, v ∉ fib B → cLoc v h = 1) →
      h ∈ stabU φ := by
  induction B using Finset.induction_on with
  | empty =>
    intro h hfin _ h1
    have : h = 1 := ext_fin hfin (one_mem _) fun v => by
      rw [h1 v (by rintro ⟨t, ht, _⟩; simp at ht), map_one]
    rw [this]
    exact one_mem _
  | insert t B _ ih =>
    intro h hfin hK h1
    obtain ⟨wt, ⟨hwtS, hwt⟩, _⟩ := hS t
    obtain ⟨x, hxfin, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion E n (fib {t}) (fib_closed {t}) h hfin
    have hxloc : x ∈ locU n wt := by
      refine Subgroup.mem_inf.2 ⟨hxfin, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
      rw [MonoidHom.mem_ker, hx u, if_neg]
      rintro ⟨t', ht', e⟩
      rw [Finset.mem_singleton] at ht'
      subst ht'
      exact hu (e.trans hwt.symm)
    have hwtf : wt ∈ fib {t} := ⟨t, Finset.mem_singleton_self t, hwt⟩
    have hxS : x ∈ stabU φ := by
      obtain ⟨k, hk, hkx⟩ := hK wt hwtS
      refine hφ wt hwtS x hxloc ⟨k, hk, ?_⟩
      rw [hx wt, if_pos hwtf, hkx]
    have hrest : x⁻¹ * h ∈ stabU φ := by
      refine ih _ (mul_mem (inv_mem hxfin) hfin) ?_ ?_
      · intro w hw
        rw [map_mul, map_inv, hx w]
        split_ifs
        · exact ⟨1, one_mem _, by rw [inv_mul_cancel]; rfl⟩
        · rw [inv_one, one_mul]; exact hK w hw
      · intro v hv
        rw [map_mul, map_inv, hx v]
        split_ifs with hvt
        · exact inv_mul_cancel _
        · rw [inv_one, one_mul]
          refine h1 v ?_
          rintro ⟨t', ht', e⟩
          rcases Finset.mem_insert.1 ht' with rfl | ht'
          · exact hvt ⟨t', Finset.mem_singleton_self _, e⟩
          · exact hv ⟨t', ht', e⟩
    have : h = x * (x⁻¹ * h) := by group
    rw [this]
    exact mul_mem hxS hrest

/- English proof (translation)
Introduce `E _ _ _ n S hS K' _ π hπ hL`. Take `⟨φ, hφπ, hφ0, hφfix⟩` from `hL`. Establish `hlev` using `(hπ.aut φ hφπ).level`. Establish `key : ∀ g : finU E n, g ∈ globLev S K' → (g : UA E n) ∈ stabU φ`. Introduce `g hg`.

Establish `hgS : ∀ w ∈ S, ∃ k ∈ K' w, k.1 = cLoc w (g : UA E n)`. Introduce `w hw`. Establish `h1` using `Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg w) hw`. Rewrite `h1` using `[Subgroup.mem_comap]`. Take `⟨k, hk, e⟩` from `Subgroup.mem_map.1 h1`.

Conclude with `⟨k, hk, e⟩`. Take `⟨T, hT⟩` from `GlobalTheory.T.mem_open_nhd_one_of_integral_eq_one_on_finset E n _ hlev (by simp)`. Establish `hbad` using `Filter.eventually_cofinite.1 (integral_eventually (g : UA E n))`. Set `B : Finset (Pl E)` to `T ∪ hbad.toFinset`. Take `⟨x, hxfin, hx⟩` from `GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion E n (fib B) (fib_closed B) (g : UA E n) g.2`.

Establish `hxS : x ∈ stabU φ`. Use `local_fixed S hS K' φ hφfix B x hxfin ?_ ?_` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[hx w]`. Use `split_ifs`.

Conclude with `hgS w hw`. Conclude with `⟨1, one_mem _, rfl⟩`. Introduce `v hv`. Rewrite using `[hx v, if_neg hv]`. Establish `hc : ∀ v, cLoc v (x⁻¹ * (g : UA E n)) = if v ∈ fib B then 1 else cLoc v (g : UA E n)`.

Introduce `v`. Rewrite using `[map_mul, map_inv, hx v]`. Use `split_ifs`. Conclude with `inv_mul_cancel _`. Rewrite using `[inv_one, one_mul]`.

Establish `hint : ∀ v, v ∉ fib B → ∀ i j : Fin n, (cLoc v (g : UA E n)) i j ∈ v.adicCompletionIntegers E ∧ (cLoc v (g : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E`. Introduce `v hv`. Assume the negation of the conclusion as `hc'`. Conclude with `hv ⟨v, Finset.mem_union_right _ (hbad.mem_toFinset.2 hc'), rfl⟩`. Establish `hrest : x⁻¹ * (g : UA E n) ∈ stabU φ`.

Use `hT ⟨x⁻¹ * (g : UA E n), mul_mem (inv_mem hxfin) g.2⟩ ?_ ?_ ?_` as an intermediate fact. Conclude with `this`. Introduce `v hv`. Express the relevant statement in the definitionally equal form `cLoc v (x⁻¹ * (g : UA E n)) = 1`. Rewrite using `[hc v, if_pos ⟨v, Finset.mem_union_left _ hv, rfl⟩]`.

Introduce `v i j`. Express the relevant statement in the definitionally equal form `(cLoc v (x⁻¹ * (g : UA E n))) i j ∈ _`. Rewrite using `[hc v]`. Use `split_ifs with hv`. Conclude with `one_entry_mem v i j`.

Conclude with `(hint v hv i j).1`. Introduce `v i j`. Express the relevant statement in the definitionally equal form `(cLoc v (x⁻¹ * (g : UA E n)))⁻¹ i j ∈ _`. Rewrite using `[hc v]`. Use `split_ifs with hv`.

Rewrite using `[inv_one]`. Conclude with `one_entry_mem v i j`. Conclude with `(hint v hv i j).2`. Establish `: (g : UA E n) = x * (x⁻¹ * (g : UA E n))` using `by group`. Rewrite using `[this]`.

Conclude with `mul_mem hxS hrest`. Introduce `hbot`. Establish `hmem : φ ∈ π ⊓ fixed (RF E n) (globLev S K')`. Use `⟨hφπ, ?_⟩` and prove the remaining obligations. Introduce `h`.

Express the relevant statement in the definitionally equal form `RU E n ((h : finU E n) : UA E n) φ = (1 : ℂˣ) • φ`. Rewrite using `[one_smul]`. Conclude with `key h h.2`. Rewrite `hmem` using `[hbot]`. Conclude with `hφ0 ((Submodule.mem_bot ℂ).1 hmem)`.
-/
theorem inf_fixed_globLev_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S →
    ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → HasLevel S π K' → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ := by
  intro E _ _ _ n S hS K' _ π hπ hL
  obtain ⟨φ, hφπ, hφ0, hφfix⟩ := hL
  have hlev := (hπ.aut φ hφπ).level
  have key : ∀ g : finU E n, g ∈ globLev S K' → (g : UA E n) ∈ stabU φ := by
    intro g hg
    have hgS : ∀ w ∈ S, ∃ k ∈ K' w, k.1 = cLoc w (g : UA E n) := by
      intro w hw
      have h1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg w) hw
      rw [Subgroup.mem_comap] at h1
      obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 h1
      exact ⟨k, hk, e⟩
    obtain ⟨T, hT⟩ := GlobalTheory.T.mem_open_nhd_one_of_integral_eq_one_on_finset E n _ hlev (by simp)
    have hbad := Filter.eventually_cofinite.1 (integral_eventually (g : UA E n))
    let B : Finset (Pl E) := T ∪ hbad.toFinset
    obtain ⟨x, hxfin, hx⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion E n (fib B) (fib_closed B) (g : UA E n) g.2
    have hxS : x ∈ stabU φ := by
      refine local_fixed S hS K' φ hφfix B x hxfin ?_ ?_
      · intro w hw
        rw [hx w]
        split_ifs
        · exact hgS w hw
        · exact ⟨1, one_mem _, rfl⟩
      · intro v hv
        rw [hx v, if_neg hv]
    have hc : ∀ v, cLoc v (x⁻¹ * (g : UA E n)) = if v ∈ fib B then 1 else cLoc v (g : UA E n) := by
      intro v
      rw [map_mul, map_inv, hx v]
      split_ifs
      · exact inv_mul_cancel _
      · rw [inv_one, one_mul]
    have hint : ∀ v, v ∉ fib B → ∀ i j : Fin n, (cLoc v (g : UA E n)) i j ∈ v.adicCompletionIntegers E ∧
        (cLoc v (g : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E := by
      intro v hv
      by_contra hc'
      exact hv ⟨v, Finset.mem_union_right _ (hbad.mem_toFinset.2 hc'), rfl⟩
    have hrest : x⁻¹ * (g : UA E n) ∈ stabU φ := by
      have := hT ⟨x⁻¹ * (g : UA E n), mul_mem (inv_mem hxfin) g.2⟩ ?_ ?_ ?_
      · exact this
      · intro v hv
        change cLoc v (x⁻¹ * (g : UA E n)) = 1
        rw [hc v, if_pos ⟨v, Finset.mem_union_left _ hv, rfl⟩]
      · intro v i j
        change (cLoc v (x⁻¹ * (g : UA E n))) i j ∈ _
        rw [hc v]
        split_ifs with hv
        · exact one_entry_mem v i j
        · exact (hint v hv i j).1
      · intro v i j
        change (cLoc v (x⁻¹ * (g : UA E n)))⁻¹ i j ∈ _
        rw [hc v]
        split_ifs with hv
        · rw [inv_one]; exact one_entry_mem v i j
        · exact (hint v hv i j).2
    have : (g : UA E n) = x * (x⁻¹ * (g : UA E n)) := by group
    rw [this]
    exact mul_mem hxS hrest
  intro hbot
  have hmem : φ ∈ π ⊓ fixed (RF E n) (globLev S K') := by
    refine ⟨hφπ, ?_⟩
    intro h
    change RU E n ((h : finU E n) : UA E n) φ = (1 : ℂˣ) • φ
    rw [one_smul]
    exact key h h.2
  rw [hbot] at hmem
  exact hφ0 ((Submodule.mem_bot ℂ).1 hmem)

end GlobalTheory.FixLev
