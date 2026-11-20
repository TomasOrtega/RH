import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise

namespace Formalism.L2.SG.Pf.RedBasicsPf

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin

attribute [local instance] Ideal.Quotient.field

variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))

abbrev RedQ : Type := I.L ⧸ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_smul (a : 𝓞 I.E) (y : Fin I.n → I.E) : ((a : 𝓞 I.E) : I.E) • y = a • y := by
  rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `z ⟨a, ha, y, hy, rfl⟩`. Rewrite using `[coe_smul]`. Conclude with `Submodule.smul_mem_smul ha hy`.

Use `Submodule.smul_le.mpr fun r hr n hn => ?_` and prove the remaining obligations. Rewrite using `[← coe_smul]`. Conclude with `Submodule.subset_span ⟨r, hr, n, hn, rfl⟩`.
-/
theorem wLat0_eq : wLat0 I w = w.asIdeal • I.L := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨a, ha, y, hy, rfl⟩
    rw [coe_smul]
    exact Submodule.smul_mem_smul ha hy
  · refine Submodule.smul_le.mpr fun r hr n hn => ?_
    rw [← coe_smul]
    exact Submodule.subset_span ⟨r, hr, n, hn, rfl⟩

/- English proof (translation)
Rewrite using `[wLat0_eq]`. Conclude with `Submodule.smul_le_right`.
-/
theorem wLat0_le : wLat0 I w ≤ I.L := by
  rw [wLat0_eq]
  exact Submodule.smul_le_right

/- English proof (translation)
Rewrite using `[coe_smul]`. Conclude with `Submodule.smul_mem _ a hz`.
-/
theorem smul_mem_wLat0 (a : 𝓞 I.E) {z : Fin I.n → I.E} (hz : z ∈ wLat0 I w) :
    ((a : 𝓞 I.E) : I.E) • z ∈ wLat0 I w := by
  rw [coe_smul]
  exact Submodule.smul_mem _ a hz

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, ha, y, hy, rfl⟩`.
-/
theorem mem_wLat0_of_mem {a : 𝓞 I.E} (ha : a ∈ w.asIdeal) {y : Fin I.n → I.E} (hy : y ∈ I.L) :
    ((a : 𝓞 I.E) : I.E) • y ∈ wLat0 I w :=
  Submodule.subset_span ⟨a, ha, y, hy, rfl⟩

/- English proof (translation)
Establish `e : wLat0 I w = (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)).map I.L.subtype`. Rewrite using `[Submodule.map_smul'', Submodule.map_subtype_top, wLat0_eq]`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzy⟩`.

Establish `hzy' : z = y` using `Subtype.ext hzy`. Rewrite using `[← hzy']` and apply the resulting hypothesis. Introduce `h`. Conclude with `⟨y, h, rfl⟩`.
-/
theorem mem_iff (y : I.L) :
    (y : Fin I.n → I.E) ∈ wLat0 I w ↔ y ∈ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) := by
  have e : wLat0 I w = (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)).map I.L.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top, wLat0_eq]
  rw [e]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : z = y := Subtype.ext hzy
    rwa [← hzy']
  · intro h
    exact ⟨y, h, rfl⟩

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : Finite (𝓞 I.E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)`. Use `letI := Fintype.ofFinite (𝓞 I.E ⧸ w.asIdeal)`. Conclude with `charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hcard])`.
-/
private lemma charP_residue_of_card_eq_prime {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) :
    CharP (𝓞 I.E ⧸ w.asIdeal) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (𝓞 I.E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 I.E ⧸ w.asIdeal)
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hcard])

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI := charP_residue_of_card_eq_prime I w hp hcard`. Use `haveI : Finite (𝓞 I.E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)`. Use `letI := Fintype.ofFinite (𝓞 I.E ⧸ w.asIdeal)`. Establish `hinj : Function.Injective (ZMod.castHom (dvd_refl p) (𝓞 I.E ⧸ w.asIdeal))` using `(ZMod.castHom (dvd_refl p) (𝓞 I.E ⧸ w.asIdeal)).injective`.

Establish `hbij` using `(Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard]⟩`. Take `⟨x, hx⟩` from `hbij.2 κ`. Use `⟨(x.val : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[← hx, ZMod.castHom_apply, Int.cast_natCast, ZMod.natCast_val]`.
-/
theorem int_surj {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    (κ : 𝓞 I.E ⧸ w.asIdeal) : ∃ c : ℤ, (c : 𝓞 I.E ⧸ w.asIdeal) = κ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := charP_residue_of_card_eq_prime I w hp hcard
  haveI : Finite (𝓞 I.E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 I.E ⧸ w.asIdeal)
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) (𝓞 I.E ⧸ w.asIdeal)) :=
    (ZMod.castHom (dvd_refl p) (𝓞 I.E ⧸ w.asIdeal)).injective
  have hbij := (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard]⟩
  obtain ⟨x, hx⟩ := hbij.2 κ
  refine ⟨(x.val : ℤ), ?_⟩
  rw [← hx, ZMod.castHom_apply, Int.cast_natCast, ZMod.natCast_val]

/- English proof (translation)
Use `haveI := charP_residue_of_card_eq_prime I w hp hcard`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_intCast, CharP.intCast_eq_zero_iff _ p]`.
-/
theorem int_mem_iff {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (c : ℤ) :
    (c : 𝓞 I.E) ∈ w.asIdeal ↔ (p : ℤ) ∣ c := by
  haveI := charP_residue_of_card_eq_prime I w hp hcard
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast, CharP.intCast_eq_zero_iff _ p]

/- English proof (translation)
Establish `h` using `(int_mem_iff I w hp hcard (p : ℤ)).mpr dvd_rfl`. Simplify using `using h`.
-/
theorem natCast_mem {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) :
    (p : 𝓞 I.E) ∈ w.asIdeal := by
  have h := (int_mem_iff I w hp hcard (p : ℤ)).mpr dvd_rfl
  simpa using h

/- English proof (translation)
The claim follows from `map_sum (Submodule.mkQ _) f Finset.univ`.
-/
theorem mk_sum' {d : ℕ} (f : Fin d → I.L) :
    (Submodule.Quotient.mk (∑ i, f i) : RedQ I w) = ∑ i, Submodule.Quotient.mk (f i) :=
  map_sum (Submodule.mkQ _) f Finset.univ

instance finite_Q : Module.Finite (𝓞 I.E ⧸ w.asIdeal) (RedQ I w) := by
  have : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.2 I.L_fg
  exact Module.Finite.of_restrictScalars_finite (𝓞 I.E) _ _

/- English proof (translation)
Establish `hκ : ∀ i, ∃ a : 𝓞 I.E, Ideal.Quotient.mk w.asIdeal a = e.repr (Submodule.Quotient.mk y) i` using `fun i => Ideal.Quotient.mk_surjective _`. Use `choose α hα using hκ`. Use `⟨α, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, mk_sum']`. Simplify using `only [← Module.Quotient.mk_smul_mk, hα, hb']`.

Rewrite using `[e.sum_repr, sub_self]`.
-/
theorem exists_lift (y : I.L) {d : ℕ} (e : Module.Basis (Fin d) (𝓞 I.E ⧸ w.asIdeal) (RedQ I w))
    (b' : Fin d → I.L) (hb' : ∀ i, Submodule.Quotient.mk (b' i) = e i) :
    ∃ α : Fin d → 𝓞 I.E, y - ∑ i, α i • b' i ∈ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) := by
  have hκ : ∀ i, ∃ a : 𝓞 I.E, Ideal.Quotient.mk w.asIdeal a = e.repr (Submodule.Quotient.mk y) i :=
    fun i => Ideal.Quotient.mk_surjective _
  choose α hα using hκ
  refine ⟨α, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, mk_sum']
  simp only [← Module.Quotient.mk_smul_mk, hα, hb']
  rw [e.sum_repr, sub_self]

/- English proof (translation)
Set `e` to `Module.finBasis (𝓞 I.E ⧸ w.asIdeal) (RedQ I w)`. Use `choose b' hb' using fun i => Submodule.Quotient.mk_surjective _ (e i)`. Establish `hli : LinearIndependent (𝓞 I.E ⧸ w.asIdeal) (Submodule.mkQ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) ∘ b')`. Establish `: (Submodule.mkQ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) ∘ b') = ⇑e` using `funext fun i => hb' i`. Rewrite using `[this]`.

Conclude with `e.linearIndependent`. Establish `hker : RingHom.ker (algebraMap (𝓞 I.E) (𝓞 I.E ⧸ w.asIdeal)) ≠ ⊤`. Rewrite using `[Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]`. Conclude with `w.isPrime.ne_top`. Establish `h` using `Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial (K := I.E) (V := Fin I.n → I.E) hker I.L.subtype Subtype.val_injective _ hli`.

Establish `h2` using `h.fintype_card_le_finrank`. Simplify using `using h2`.
-/
theorem finrank_le : Module.finrank (𝓞 I.E ⧸ w.asIdeal) (RedQ I w) ≤ I.n := by
  let e := Module.finBasis (𝓞 I.E ⧸ w.asIdeal) (RedQ I w)
  choose b' hb' using fun i => Submodule.Quotient.mk_surjective _ (e i)
  have hli : LinearIndependent (𝓞 I.E ⧸ w.asIdeal)
      (Submodule.mkQ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) ∘ b') := by
    have : (Submodule.mkQ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) ∘ b') = ⇑e := funext fun i => hb' i
    rw [this]; exact e.linearIndependent
  have hker : RingHom.ker (algebraMap (𝓞 I.E) (𝓞 I.E ⧸ w.asIdeal)) ≠ ⊤ := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact w.isPrime.ne_top
  have h := Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial (K := I.E) (V := Fin I.n → I.E) hker
    I.L.subtype Subtype.val_injective _ hli
  have h2 := h.fintype_card_le_finrank
  simpa using h2

/- English proof (translation)
Set `e` to `Module.finBasis (𝓞 I.E ⧸ w.asIdeal) (RedQ I w)`. Use `choose b' hb' using fun i => Submodule.Quotient.mk_surjective _ (e i)`. Set `N : Submodule (𝓞 I.E) (Fin I.n → I.E)` to `Submodule.span (𝓞 I.E) (Set.range fun i => (b' i : Fin I.n → I.E))`. Establish `hsup : I.L ≤ N ⊔ w.asIdeal • I.L`. Introduce `y hy`.

Take `⟨α, hα⟩` from `exists_lift I w ⟨y, hy⟩ e b' hb'`. Rewrite `hα` using `[← mem_iff, wLat0_eq]`. Establish `hsum : (((∑ i, α i • b' i : I.L)) : Fin I.n → I.E) ∈ N`. Rewrite using `[Submodule.coe_sum]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `: y = ((∑ i, α i • b' i : I.L) : Fin I.n → I.E) + (((⟨y, hy⟩ : I.L) - ∑ i, α i • b' i : I.L) : Fin I.n → I.E)`. Rewrite using `[Submodule.coe_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup hsum hα`.

Take `⟨r, hr1, hrL⟩` from `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup I.L_fg le_rfl hsup`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Apply `w.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`.

Simplify using `using w.asIdeal.neg_mem hr1`. Establish `hrE : ((r : 𝓞 I.E) : I.E) ≠ 0` using `RingOfIntegers.coe_ne_zero_iff.2 hr0`. Establish `hspan : Submodule.span I.E (Set.range fun i => (b' i : Fin I.n → I.E)) = ⊤`. Rewrite using `[eq_top_iff, ← I.L_span, Submodule.span_le]`. Introduce `y hy`.

Establish `hry : r • y ∈ N` using `hrL (Submodule.smul_mem_pointwise_smul y r I.L hy)`. Establish `h2 : r • y ∈ Submodule.span I.E (Set.range fun i => (b' i : Fin I.n → I.E))` using `Submodule.span_le_restrictScalars (𝓞 I.E) I.E _ hry`. Establish `h3 : y = ((r : 𝓞 I.E) : I.E)⁻¹ • (r • y)`. Rewrite using `[← coe_smul, smul_smul, inv_mul_cancel₀ hrE, one_smul]`. Rewrite using `[h3]`.

Conclude with `Submodule.smul_mem _ _ h2`. Establish `h` using `finrank_range_le_card (R := I.E) (fun i => (b' i : Fin I.n → I.E))`. Rewrite `h` using `[Set.finrank, hspan, finrank_top, Module.finrank_fin_fun]`. Simplify using `using h`.
-/
theorem le_finrank : I.n ≤ Module.finrank (𝓞 I.E ⧸ w.asIdeal) (RedQ I w) := by
  let e := Module.finBasis (𝓞 I.E ⧸ w.asIdeal) (RedQ I w)
  choose b' hb' using fun i => Submodule.Quotient.mk_surjective _ (e i)
  let N : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
    Submodule.span (𝓞 I.E) (Set.range fun i => (b' i : Fin I.n → I.E))
  have hsup : I.L ≤ N ⊔ w.asIdeal • I.L := by
    intro y hy
    obtain ⟨α, hα⟩ := exists_lift I w ⟨y, hy⟩ e b' hb'
    rw [← mem_iff, wLat0_eq] at hα
    have hsum : (((∑ i, α i • b' i : I.L)) : Fin I.n → I.E) ∈ N := by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have : y = ((∑ i, α i • b' i : I.L) : Fin I.n → I.E) +
        (((⟨y, hy⟩ : I.L) - ∑ i, α i • b' i : I.L) : Fin I.n → I.E) := by
      rw [Submodule.coe_sub]; abel
    rw [this]
    exact Submodule.add_mem_sup hsum hα
  obtain ⟨r, hr1, hrL⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup I.L_fg le_rfl hsup
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using w.asIdeal.neg_mem hr1
  have hrE : ((r : 𝓞 I.E) : I.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hr0
  have hspan : Submodule.span I.E (Set.range fun i => (b' i : Fin I.n → I.E)) = ⊤ := by
    rw [eq_top_iff, ← I.L_span, Submodule.span_le]
    intro y hy
    have hry : r • y ∈ N := hrL (Submodule.smul_mem_pointwise_smul y r I.L hy)
    have h2 : r • y ∈ Submodule.span I.E (Set.range fun i => (b' i : Fin I.n → I.E)) :=
      Submodule.span_le_restrictScalars (𝓞 I.E) I.E _ hry
    have h3 : y = ((r : 𝓞 I.E) : I.E)⁻¹ • (r • y) := by
      rw [← coe_smul, smul_smul, inv_mul_cancel₀ hrE, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ h2
  have h := finrank_range_le_card (R := I.E) (fun i => (b' i : Fin I.n → I.E))
  rw [Set.finrank, hspan, finrank_top, Module.finrank_fin_fun] at h
  simpa using h

/- English proof (translation)
The claim follows from `le_antisymm (finrank_le I w) (le_finrank I w)`.
-/
theorem finrank_eq : Module.finrank (𝓞 I.E ⧸ w.asIdeal) (RedQ I w) = I.n :=
  le_antisymm (finrank_le I w) (le_finrank I w)

/- English proof (translation)
Set `e : Module.Basis (Fin I.n) (𝓞 I.E ⧸ w.asIdeal) (RedQ I w)` to `Module.finBasisOfFinrankEq _ _ (finrank_eq I w)`. Establish `hl : ∀ i, ∃ b : I.L, Submodule.Quotient.mk b = e i` using `fun i => Submodule.Quotient.mk_surjective _ (e i)`. Use `choose b' hb' using hl`. Use `⟨fun i => (b' i : Fin I.n → I.E), fun i => (b' i).2, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨α, hα⟩` from `exists_lift I w ⟨y, hy⟩ e b' hb'`.

Use `choose c hc using fun i => int_surj I w hp hcard (Ideal.Quotient.mk w.asIdeal (α i))`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `h1 : (((⟨y, hy⟩ : I.L) - ∑ i, α i • b' i : I.L) : Fin I.n → I.E) ∈ wLat0 I w` using `(mem_iff I w _).mpr hα`. Establish `h2 : ∀ i, (((α i : 𝓞 I.E) : I.E) - (c i : I.E)) • (b' i : Fin I.n → I.E) ∈ wLat0 I w`. Introduce `i`.

Establish `hm : α i - (c i : 𝓞 I.E) ∈ w.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, hc i, sub_self]`. Use `mem_wLat0_of_mem I w hm (b' i).2` as an intermediate fact. Simplify using `using this`. Establish `key : y - ∑ i, (c i : I.E) • (b' i : Fin I.n → I.E) = (((⟨y, hy⟩ : I.L) - ∑ i, α i • b' i : I.L) : Fin I.n → I.E) + ∑ i, (((α i : 𝓞 I.E) : I.E) - (c i : I.E)) • (b' i : Fin I.n → I.E)`.

Simplify using `only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, ← coe_smul, sub_smul, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Rewrite using `[key]`. Conclude with `Submodule.add_mem _ h1 (Submodule.sum_mem _ fun i _ => h2 i)`.
-/
theorem exists_redBasis {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) :
    ∃ b : Fin I.n → (Fin I.n → I.E), IsRedBasis0 I w b := by
  classical
  let e : Module.Basis (Fin I.n) (𝓞 I.E ⧸ w.asIdeal) (RedQ I w) :=
    Module.finBasisOfFinrankEq _ _ (finrank_eq I w)
  have hl : ∀ i, ∃ b : I.L, Submodule.Quotient.mk b = e i := fun i => Submodule.Quotient.mk_surjective _ (e i)
  choose b' hb' using hl
  refine ⟨fun i => (b' i : Fin I.n → I.E), fun i => (b' i).2, fun y hy => ?_⟩
  obtain ⟨α, hα⟩ := exists_lift I w ⟨y, hy⟩ e b' hb'
  choose c hc using fun i => int_surj I w hp hcard (Ideal.Quotient.mk w.asIdeal (α i))
  refine ⟨c, ?_⟩
  have h1 : (((⟨y, hy⟩ : I.L) - ∑ i, α i • b' i : I.L) : Fin I.n → I.E) ∈ wLat0 I w := (mem_iff I w _).mpr hα
  have h2 : ∀ i, (((α i : 𝓞 I.E) : I.E) - (c i : I.E)) • (b' i : Fin I.n → I.E) ∈ wLat0 I w := by
    intro i
    have hm : α i - (c i : 𝓞 I.E) ∈ w.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, hc i, sub_self]
    have := mem_wLat0_of_mem I w hm (b' i).2
    simpa using this
  have key : y - ∑ i, (c i : I.E) • (b' i : Fin I.n → I.E) =
      (((⟨y, hy⟩ : I.L) - ∑ i, α i • b' i : I.L) : Fin I.n → I.E) +
        ∑ i, (((α i : 𝓞 I.E) : I.E) - (c i : I.E)) • (b' i : Fin I.n → I.E) := by
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, ← coe_smul, sub_smul,
      Finset.sum_sub_distrib]
    abel
  rw [key]
  exact Submodule.add_mem _ h1 (Submodule.sum_mem _ fun i _ => h2 i)

/- English proof (translation)
Set `v : Fin I.n → RedQ I w` to `fun i => Submodule.Quotient.mk ⟨b i, hb.1 i⟩`. Establish `hcoe : ∀ d : Fin I.n → ℤ, ((∑ i, (d i : 𝓞 I.E) • (⟨b i, hb.1 i⟩ : I.L) : I.L) : Fin I.n → I.E) = ∑ i, (d i : I.E) • b i`. Introduce `d`. Simplify using `[← coe_smul]`. Establish `hmk : ∀ d : Fin I.n → ℤ, ∑ i, Ideal.Quotient.mk w.asIdeal (d i : 𝓞 I.E) • v i = Submodule.Quotient.mk (∑ i, (d i : 𝓞 I.E) • (⟨b i, hb.1 i⟩ : I.L))`.

Introduce `d`. Rewrite using `[mk_sum']`. Simplify using `only [v, Module.Quotient.mk_smul_mk]`. Establish `hspan : ⊤ ≤ Submodule.span (𝓞 I.E ⧸ w.asIdeal) (Set.range v)`. Introduce and unpack `q -`.

Take `⟨⟨y, hy⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨c', hc'⟩` from `hb.2 y hy`. Establish `hq : (Submodule.Quotient.mk (⟨y, hy⟩ : I.L) : RedQ I w) = ∑ i, Ideal.Quotient.mk w.asIdeal (c' i : 𝓞 I.E) • v i`. Rewrite using `[hmk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero, ← mem_iff, Submodule.coe_sub, hcoe]`. Conclude with `hc'`.

Rewrite using `[hq]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hli` using `linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by rw [Fintype.card_fin, finrank_eq])`. Establish `hz : ∑ i, Ideal.Quotient.mk w.asIdeal (c i : 𝓞 I.E) • v i = 0`. Rewrite using `[hmk, Submodule.Quotient.mk_eq_zero, ← mem_iff, hcoe]`.

Conclude with `hc`. Establish `h0` using `Fintype.linearIndependent_iff.mp hli _ hz i`. Rewrite `h0` using `[Ideal.Quotient.eq_zero_iff_mem, int_mem_iff I w hp hcard]`. Conclude with `h0`.
-/
theorem redBasis_indep {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {b : Fin I.n → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) (c : Fin I.n → ℤ)
    (hc : ∑ i, (c i : I.E) • b i ∈ wLat0 I w) (i : Fin I.n) : (p : ℤ) ∣ c i := by
  classical
  let v : Fin I.n → RedQ I w := fun i => Submodule.Quotient.mk ⟨b i, hb.1 i⟩
  have hcoe : ∀ d : Fin I.n → ℤ,
      ((∑ i, (d i : 𝓞 I.E) • (⟨b i, hb.1 i⟩ : I.L) : I.L) : Fin I.n → I.E) = ∑ i, (d i : I.E) • b i := by
    intro d
    simp [← coe_smul]
  have hmk : ∀ d : Fin I.n → ℤ, ∑ i, Ideal.Quotient.mk w.asIdeal (d i : 𝓞 I.E) • v i =
      Submodule.Quotient.mk (∑ i, (d i : 𝓞 I.E) • (⟨b i, hb.1 i⟩ : I.L)) := by
    intro d
    rw [mk_sum']
    simp only [v, Module.Quotient.mk_smul_mk]
  have hspan : ⊤ ≤ Submodule.span (𝓞 I.E ⧸ w.asIdeal) (Set.range v) := by
    rintro q -
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨c', hc'⟩ := hb.2 y hy
    have hq : (Submodule.Quotient.mk (⟨y, hy⟩ : I.L) : RedQ I w) =
        ∑ i, Ideal.Quotient.mk w.asIdeal (c' i : 𝓞 I.E) • v i := by
      rw [hmk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero, ← mem_iff,
        Submodule.coe_sub, hcoe]
      exact hc'
    rw [hq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by rw [Fintype.card_fin, finrank_eq])
  have hz : ∑ i, Ideal.Quotient.mk w.asIdeal (c i : 𝓞 I.E) • v i = 0 := by
    rw [hmk, Submodule.Quotient.mk_eq_zero, ← mem_iff, hcoe]
    exact hc
  have h0 := Fintype.linearIndependent_iff.mp hli _ hz i
  rw [Ideal.Quotient.eq_zero_iff_mem, int_mem_iff I w hp hcard] at h0
  exact h0

/- English proof (translation)
Use `show Submodule.span _ _ ≤ S`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨⟨v, hv⟩, rfl⟩`. Use `show iv I v ∈ S`. Rewrite `hv` using `[wLat0]`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, y, hy, rfl⟩` from `hx`. Conclude with `h a ha y hy`. Consider the case `zero => rw [DictLat.iv_zero]`.

Conclude with `S.zero_mem`. Consider the case `add x y _ _ hx hy => rw [DictLat.iv_add]`. Conclude with `S.add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[DictLat.iv_smulO]`.

Conclude with `S.smul_mem (⟨Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E), DictLat.inclE_int I ⟨a, rfl⟩⟩ : IntAf I.F I.E) hx`.
-/
theorem lamAf_w_le (S : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F))
    (h : ∀ a ∈ w.asIdeal, ∀ y ∈ I.L, iv I (((a : 𝓞 I.E) : I.E) • y) ∈ S) :
    lamAf (F := I.F) (wLat0 I w) ≤ S := by
  show Submodule.span _ _ ≤ S
  rw [Submodule.span_le]
  rintro _ ⟨⟨v, hv⟩, rfl⟩
  show iv I v ∈ S
  rw [wLat0] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    exact h a ha y hy
  | zero => rw [DictLat.iv_zero]; exact S.zero_mem
  | add x y _ _ hx hy => rw [DictLat.iv_add]; exact S.add_mem hx hy
  | smul a x _ hx =>
    rw [DictLat.iv_smulO]
    exact S.smul_mem (⟨Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E), DictLat.inclE_int I ⟨a, rfl⟩⟩ : IntAf I.F I.E) hx

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩`.
-/
theorem iv_mem_w {v : Fin I.n → I.E} (hv : v ∈ wLat0 I w) : iv I v ∈ lamAf (F := I.F) (wLat0 I w) :=
  Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨⟨x, h x.2⟩, rfl⟩`.
-/
theorem lamAf_mono {L₁ L₂ : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : L₁ ≤ L₂) :
    lamAf (F := I.F) L₁ ≤ lamAf (F := I.F) L₂ := by
  refine Submodule.span_mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x, h x.2⟩, rfl⟩

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, rfl⟩` from `hx`. Establish `e : (Formalism.UG.inclE (F` using `I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) • fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((y : Fin I.n → I.E) i)) = iv I (((a : 𝓞 I.E) : I.E) • (y : Fin I.n → I.E)) := by`. Use function extensionality and compare the values at `i`.

Simplify using `only [iv, Pi.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[e]`. Conclude with `iv_mem_w I w (mem_wLat0_of_mem I w ha y.2)`. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem smul_mem {a : 𝓞 I.E} (ha : a ∈ w.asIdeal) {u : Fin I.n → I.E ⊗[I.F] Af I.F} (hu : u ∈ I.Lf) :
    Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) • u ∈ lamAf (F := I.F) (wLat0 I w) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    have e : (Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) •
        fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((y : Fin I.n → I.E) i)) =
        iv I (((a : 𝓞 I.E) : I.E) • (y : Fin I.n → I.E)) := by
      funext i
      simp only [iv, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [e]
    exact iv_mem_w I w (mem_wLat0_of_mem I w ha y.2)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

/- English proof (translation)
Take `⟨l, hl, y', hy', he⟩` from `lattice_dense I p hp.pos y hy`. Use `⟨l, hl, ?_⟩` and prove the remaining obligations. Rewrite using `[he, add_sub_cancel_left]`. Use `smul_mem I w (natCast_mem I w hp hcard) hy'` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal.

Simplify using the standard rewrite rules.
-/
theorem dense {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    ∃ l ∈ I.L, y - iv I l ∈ lamAf (F := I.F) (wLat0 I w) := by
  obtain ⟨l, hl, y', hy', he⟩ := lattice_dense I p hp.pos y hy
  refine ⟨l, hl, ?_⟩
  rw [he, add_sub_cancel_left]
  have := smul_mem I w (natCast_mem I w hp hcard) hy'
  convert this using 2
  simp

/- English proof (translation)
Establish `hx' : ∀ u, u ∈ I.Lf ↔ I.fmat x *ᵥ u ∈ I.Lf` using `hx`. Set `S : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F)` to `(lamAf (F := I.F) (wLat0 I w)).comap ((Matrix.mulVecLin (I.fmat x)).restrictScalars (IntAf I.F I.E))`. Use `lamAf_w_le I w S (fun a ha y hy => ?_) hv` and prove the remaining obligations. Use `show I.fmat x *ᵥ iv I (((a : 𝓞 I.E) : I.E) • y) ∈ lamAf (F := I.F) (wLat0 I w)`. Rewrite using `[DictLat.iv_smulE, Matrix.mulVec_smul]`.

Conclude with `smul_mem I w ha ((hx' _).1 (DictLat.iv_mem I hy))`.
-/
theorem stab_w {x : I.Gf} (hx : x ∈ I.Kset) {v : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hv : v ∈ lamAf (F := I.F) (wLat0 I w)) : I.fmat x *ᵥ v ∈ lamAf (F := I.F) (wLat0 I w) := by
  have hx' : ∀ u, u ∈ I.Lf ↔ I.fmat x *ᵥ u ∈ I.Lf := hx
  let S : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    (lamAf (F := I.F) (wLat0 I w)).comap ((Matrix.mulVecLin (I.fmat x)).restrictScalars (IntAf I.F I.E))
  refine lamAf_w_le I w S (fun a ha y hy => ?_) hv
  show I.fmat x *ᵥ iv I (((a : 𝓞 I.E) : I.E) • y) ∈ lamAf (F := I.F) (wLat0 I w)
  rw [DictLat.iv_smulE, Matrix.mulVec_smul]
  exact smul_mem I w ha ((hx' _).1 (DictLat.iv_mem I hy))

/- English proof (translation)
Establish `hne : w.asIdeal ^ 2 ≠ w.asIdeal`. Introduce `h`. Establish `h0 : w.asIdeal ≠ 0` using `by rw [Ideal.zero_eq_bot]; exact w.ne_bot`. Establish `: w.asIdeal * w.asIdeal = w.asIdeal * 1` using `by rw [mul_one, ← sq, h]`. Establish `h1` using `mul_left_cancel₀ h0 this`.

Conclude with `w.isPrime.ne_top (by rw [h1, Ideal.one_eq_top])`. Establish `hlt : w.asIdeal ^ 2 < w.asIdeal` using `lt_of_le_of_ne (Ideal.pow_le_self two_ne_zero) hne`. Take `⟨t, htw, ht2⟩` from `SetLike.exists_of_lt hlt`. Establish `ht0 : t ≠ 0` using `by rintro rfl; exact ht2 (zero_mem _)`. Take `⟨w', hw'⟩ : w.asIdeal ∣ Ideal.span {t}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 htw)`.

Establish `hw'w : ¬ w' ≤ w.asIdeal`. Introduce `h`. Apply `ht2` to reduce the goal to its premises. Establish `: Ideal.span {t} ≤ w.asIdeal ^ 2` using `by rw [hw', sq]; exact Ideal.mul_mono_right h`. Conclude with `this (Ideal.mem_span_singleton_self t)`.

Take `⟨β, hβ, hβw⟩` from `SetLike.not_le_iff_exists.1 hw'w`. Use `⟨t, β, htw, ht0, fun a ha => ?_, hβw⟩` and prove the remaining obligations. Establish `: a * β ∈ Ideal.span {t}` using `by rw [hw']; exact Ideal.mul_mem_mul ha hβ`. Take `⟨g, hg⟩` from `Ideal.mem_span_singleton'.1 this`. Conclude with `⟨g, by rw [mul_comm β, ← hg, mul_comm]⟩`.
-/
theorem exists_ideal_element_not_mem : ∃ t β : 𝓞 I.E, t ∈ w.asIdeal ∧ t ≠ 0 ∧ (∀ a ∈ w.asIdeal, ∃ g, β * a = t * g) ∧
    β ∉ w.asIdeal := by
  have hne : w.asIdeal ^ 2 ≠ w.asIdeal := by
    intro h
    have h0 : w.asIdeal ≠ 0 := by rw [Ideal.zero_eq_bot]; exact w.ne_bot
    have : w.asIdeal * w.asIdeal = w.asIdeal * 1 := by rw [mul_one, ← sq, h]
    have h1 := mul_left_cancel₀ h0 this
    exact w.isPrime.ne_top (by rw [h1, Ideal.one_eq_top])
  have hlt : w.asIdeal ^ 2 < w.asIdeal := lt_of_le_of_ne (Ideal.pow_le_self two_ne_zero) hne
  obtain ⟨t, htw, ht2⟩ := SetLike.exists_of_lt hlt
  have ht0 : t ≠ 0 := by rintro rfl; exact ht2 (zero_mem _)
  obtain ⟨w', hw'⟩ : w.asIdeal ∣ Ideal.span {t} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 htw)
  have hw'w : ¬ w' ≤ w.asIdeal := by
    intro h
    apply ht2
    have : Ideal.span {t} ≤ w.asIdeal ^ 2 := by rw [hw', sq]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self t)
  obtain ⟨β, hβ, hβw⟩ := SetLike.not_le_iff_exists.1 hw'w
  refine ⟨t, β, htw, ht0, fun a ha => ?_, hβw⟩
  have : a * β ∈ Ideal.span {t} := by rw [hw']; exact Ideal.mul_mem_mul ha hβ
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨g, by rw [mul_comm β, ← hg, mul_comm]⟩

/- English proof (translation)
Establish `hvL : v ∈ I.L` using `lattice_intersection' I v (lamAf_mono I (wLat0_le I w) hv)`. Take `⟨t, β, htw, ht0, hβ, hβw⟩` from `exists_ideal_element_not_mem I w`. Set `φβ : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[IntAf I.F I.E] (Fin I.n → I.E ⊗[I.F] Af I.F)` to `((Formalism.UG.inclE (F := I.F) (Af I.F) ((β : 𝓞 I.E) : I.E)) • (LinearMap.id : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[I.E ⊗[I.F] Af I.F] _)).restrictScalars _`. Set `φt : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[IntAf I.F I.E] (Fin I.n → I.E ⊗[I.F] Af I.F)` to `((Formalism.UG.inclE (F := I.F) (Af I.F) ((t : 𝓞 I.E) : I.E)) • (LinearMap.id : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[I.E ⊗[I.F] Af I.F] _)).restrictScalars _`. Establish `hle : lamAf (F` using `I.F) (wLat0 I w) ≤ (I.Lf.map φt).comap φβ := by`.

Use `lamAf_w_le I w _ (fun a ha y hy => ?_)` and prove the remaining obligations. Take `⟨g, hg⟩` from `hβ a ha`. Rewrite using `[Submodule.mem_comap, Submodule.mem_map]`. Use `⟨iv I (((g : 𝓞 I.E) : I.E) • y), DictLat.iv_mem I (by rw [coe_smul]; exact I.L.smul_mem g hy), ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.inclE (F := I.F) (Af I.F) ((t : 𝓞 I.E) : I.E) • iv I (((g : 𝓞 I.E) : I.E) • y) = Formalism.UG.inclE (F := I.F) (Af I.F) ((β : 𝓞 I.E) : I.E) • iv I (((a : 𝓞 I.E) : I.E) • y)`.

Rewrite using `[DictLat.iv_smulE, DictLat.iv_smulE, smul_smul, smul_smul]`. Use `congr 1`. Simplify using `only [← map_mul, hg]`. Take `⟨u, hu, hue⟩` from `(Submodule.mem_map).1 (hle hv)`. Establish `hue' : Formalism.UG.inclE (F` using `I.F) (Af I.F) ((t : 𝓞 I.E) : I.E) • u = Formalism.UG.inclE (F := I.F) (Af I.F) ((β : 𝓞 I.E) : I.E) • iv I v := hue`.

Establish `htE : ((t : 𝓞 I.E) : I.E) ≠ 0` using `RingOfIntegers.coe_ne_zero_iff.2 ht0`. Establish `hz : iv I (((t : 𝓞 I.E) : I.E)⁻¹ • ((β : 𝓞 I.E) : I.E) • v) = u`. Rewrite using `[DictLat.iv_smulE, DictLat.iv_smulE, ← hue', smul_smul, ← map_mul, inv_mul_cancel₀ htE, map_one, one_smul]`. Establish `hzL : ((t : 𝓞 I.E) : I.E)⁻¹ • ((β : 𝓞 I.E) : I.E) • v ∈ I.L` using `lattice_intersection' I _ (by rw [hz]; exact hu)`. Establish `hβv : ((β : 𝓞 I.E) : I.E) • v ∈ wLat0 I w`.

Establish `e1 : ((β : 𝓞 I.E) : I.E) • v = ((t : 𝓞 I.E) : I.E) • (((t : 𝓞 I.E) : I.E)⁻¹ • ((β : 𝓞 I.E) : I.E) • v)`. Rewrite using `[smul_smul, mul_inv_cancel₀ htE, one_smul]`. Rewrite using `[e1]`. Conclude with `mem_wLat0_of_mem I w htw hzL`. Take `⟨γ, i, hi, hγ⟩` from `Ideal.IsMaximal.exists_inv (inferInstance : w.asIdeal.IsMaximal) hβw`.

Establish `hγ' : ((γ : 𝓞 I.E) : I.E) * ((β : 𝓞 I.E) : I.E) + ((i : 𝓞 I.E) : I.E) = 1`. Use `congrArg (fun z : 𝓞 I.E => (z : I.E)) hγ` as an intermediate fact. Simplify using `using this`. Establish `e2 : v = ((γ : 𝓞 I.E) : I.E) • (((β : 𝓞 I.E) : I.E) • v) + ((i : 𝓞 I.E) : I.E) • v`. Rewrite using `[smul_smul, ← add_smul, hγ', one_smul]`.

Rewrite using `[e2]`. Conclude with `Submodule.add_mem _ (smul_mem_wLat0 I w γ hβv) (mem_wLat0_of_mem I w hi hvL)`.
-/
theorem inter {v : Fin I.n → I.E} (hv : iv I v ∈ lamAf (F := I.F) (wLat0 I w)) : v ∈ wLat0 I w := by
  have hvL : v ∈ I.L := lattice_intersection' I v (lamAf_mono I (wLat0_le I w) hv)
  obtain ⟨t, β, htw, ht0, hβ, hβw⟩ := exists_ideal_element_not_mem I w
  let φβ : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[IntAf I.F I.E] (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    ((Formalism.UG.inclE (F := I.F) (Af I.F) ((β : 𝓞 I.E) : I.E)) • (LinearMap.id : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[I.E ⊗[I.F] Af I.F] _)).restrictScalars _
  let φt : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[IntAf I.F I.E] (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    ((Formalism.UG.inclE (F := I.F) (Af I.F) ((t : 𝓞 I.E) : I.E)) • (LinearMap.id : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₗ[I.E ⊗[I.F] Af I.F] _)).restrictScalars _
  have hle : lamAf (F := I.F) (wLat0 I w) ≤ (I.Lf.map φt).comap φβ := by
    refine lamAf_w_le I w _ (fun a ha y hy => ?_)
    obtain ⟨g, hg⟩ := hβ a ha
    rw [Submodule.mem_comap, Submodule.mem_map]
    refine ⟨iv I (((g : 𝓞 I.E) : I.E) • y),
      DictLat.iv_mem I (by rw [coe_smul]; exact I.L.smul_mem g hy), ?_⟩
    show Formalism.UG.inclE (F := I.F) (Af I.F) ((t : 𝓞 I.E) : I.E) • iv I (((g : 𝓞 I.E) : I.E) • y) =
      Formalism.UG.inclE (F := I.F) (Af I.F) ((β : 𝓞 I.E) : I.E) • iv I (((a : 𝓞 I.E) : I.E) • y)
    rw [DictLat.iv_smulE, DictLat.iv_smulE, smul_smul, smul_smul]
    congr 1
    simp only [← map_mul, hg]
  obtain ⟨u, hu, hue⟩ := (Submodule.mem_map).1 (hle hv)
  have hue' : Formalism.UG.inclE (F := I.F) (Af I.F) ((t : 𝓞 I.E) : I.E) • u = Formalism.UG.inclE (F := I.F) (Af I.F) ((β : 𝓞 I.E) : I.E) • iv I v := hue
  have htE : ((t : 𝓞 I.E) : I.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ht0
  have hz : iv I (((t : 𝓞 I.E) : I.E)⁻¹ • ((β : 𝓞 I.E) : I.E) • v) = u := by
    rw [DictLat.iv_smulE, DictLat.iv_smulE, ← hue', smul_smul, ← map_mul, inv_mul_cancel₀ htE, map_one,
      one_smul]
  have hzL : ((t : 𝓞 I.E) : I.E)⁻¹ • ((β : 𝓞 I.E) : I.E) • v ∈ I.L :=
    lattice_intersection' I _ (by rw [hz]; exact hu)
  have hβv : ((β : 𝓞 I.E) : I.E) • v ∈ wLat0 I w := by
    have e1 : ((β : 𝓞 I.E) : I.E) • v =
        ((t : 𝓞 I.E) : I.E) • (((t : 𝓞 I.E) : I.E)⁻¹ • ((β : 𝓞 I.E) : I.E) • v) := by
      rw [smul_smul, mul_inv_cancel₀ htE, one_smul]
    rw [e1]
    exact mem_wLat0_of_mem I w htw hzL
  obtain ⟨γ, i, hi, hγ⟩ := Ideal.IsMaximal.exists_inv (inferInstance : w.asIdeal.IsMaximal) hβw
  have hγ' : ((γ : 𝓞 I.E) : I.E) * ((β : 𝓞 I.E) : I.E) + ((i : 𝓞 I.E) : I.E) = 1 := by
    have := congrArg (fun z : 𝓞 I.E => (z : I.E)) hγ
    simpa using this
  have e2 : v = ((γ : 𝓞 I.E) : I.E) • (((β : 𝓞 I.E) : I.E) • v) + ((i : 𝓞 I.E) : I.E) • v := by
    rw [smul_smul, ← add_smul, hγ', one_smul]
  rw [e2]
  exact Submodule.add_mem _ (smul_mem_wLat0 I w γ hβv) (mem_wLat0_of_mem I w hi hvL)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [iv, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_sum, map_mul, map_intCast]`.
-/
theorem iv_lin (l : Fin I.n → I.E) {m : ℕ} (b : Fin m → Fin I.n → I.E) (c : Fin m → ℤ) :
    iv I (l - ∑ i, (c i : I.E) • b i) = iv I l - ∑ i, (c i : I.E ⊗[I.F] Af I.F) • iv I (b i) := by
  funext k
  simp only [iv, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_sum, map_mul,
    map_intCast]

/- English proof (translation)
Take `⟨l, hl, hyl⟩` from `dense I w hp hcard hy`. Take `⟨c, hc⟩` from `hb.2 l hl`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `h2` using `iv_mem_w I w hc`. Rewrite `h2` using `[iv_lin]`.

Establish `h3` using `Submodule.add_mem _ hyl h2`. Rewrite `h3` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem coords {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    ∃ c : Fin m → ℤ, y - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ lamAf (F := I.F) (wLat0 I w) := by
  obtain ⟨l, hl, hyl⟩ := dense I w hp hcard hy
  obtain ⟨c, hc⟩ := hb.2 l hl
  refine ⟨c, ?_⟩
  have h2 := iv_mem_w I w hc
  rw [iv_lin] at h2
  have h3 := Submodule.add_mem _ hyl h2
  rwa [sub_add_sub_cancel] at h3

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hd : (p : ℤ) ∣ ((c : ZMod p).val : ℤ) - c`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Simplify using the standard rewrite rules. Take `⟨k, hk⟩` from `hd`.

Establish `hm : (p : 𝓞 I.E) * (k : 𝓞 I.E) ∈ w.asIdeal` using `Ideal.mul_mem_right _ _ (natCast_mem I w hp hcard)`. Establish `h1` using `iv_mem_w I w (mem_wLat0_of_mem I w hm hz)`. Establish `e : ((((c : ZMod p)).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I z - (c : I.E ⊗[I.F] Af I.F) • iv I z = iv I ((((p : 𝓞 I.E) * (k : 𝓞 I.E) : 𝓞 I.E) : I.E) • z)`. Use function extensionality and compare the values at `i`. Establish `hk' : ((((c : ZMod p).val : ℤ) - c : ℤ) : I.E ⊗[I.F] Af I.F) = ((p * k : ℤ) : I.E ⊗[I.F] Af I.F)`.

Rewrite using `[hk]`. Move the coercions through the operations in `at hk'`. Simplify using `only [iv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Rewrite using `[← sub_mul, hk', map_mul, map_mul, map_natCast]`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `h1`.
-/
theorem val_sub {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {z : Fin I.n → I.E} (hz : z ∈ I.L) (c : ℤ) :
    ((((c : ZMod p)).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I z - (c : I.E ⊗[I.F] Af I.F) • iv I z ∈
      lamAf (F := I.F) (wLat0 I w) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hd : (p : ℤ) ∣ ((c : ZMod p).val : ℤ) - c := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp
  obtain ⟨k, hk⟩ := hd
  have hm : (p : 𝓞 I.E) * (k : 𝓞 I.E) ∈ w.asIdeal := Ideal.mul_mem_right _ _ (natCast_mem I w hp hcard)
  have h1 := iv_mem_w I w (mem_wLat0_of_mem I w hm hz)
  have e : ((((c : ZMod p)).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I z - (c : I.E ⊗[I.F] Af I.F) • iv I z =
      iv I ((((p : 𝓞 I.E) * (k : 𝓞 I.E) : 𝓞 I.E) : I.E) • z) := by
    funext i
    have hk' : ((((c : ZMod p).val : ℤ) - c : ℤ) : I.E ⊗[I.F] Af I.F) = ((p * k : ℤ) : I.E ⊗[I.F] Af I.F) := by
      rw [hk]
    push_cast at hk'
    simp only [iv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [← sub_mul, hk', map_mul, map_mul, map_natCast]
    simp
  rw [e]
  exact h1

end Formalism.L2.SG.Pf.RedBasicsPf
