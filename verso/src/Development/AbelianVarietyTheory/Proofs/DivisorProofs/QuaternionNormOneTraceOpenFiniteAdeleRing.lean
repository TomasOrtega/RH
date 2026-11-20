import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology RestrictedProduct

noncomputable section

namespace GlobalTheory.QSA.FinAdele

variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)}

variable {F : Type} [Field F] [NumberField F]

def loc {a b : F} (v : HeightOneSpectrum (𝓞 F))
    (x : ℍ[FiniteAdeleRing (𝓞 F) F, algebraMap F (FiniteAdeleRing (𝓞 F) F) a,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) b]) :
    ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b] :=
  ⟨x.re v, x.imI v, x.imJ v, x.imK v⟩

open NumberField IsDedekindDomain in
open scoped Quaternion Topology RestrictedProduct in
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
Establish `h : W ∈ Filter.comap _root_.GlobalTheory.QSA.coords (𝓝 (_root_.GlobalTheory.QSA.coords g))`. Rewrite using `[← nhds_induced]`. Conclude with `hW`. Take `⟨P, hP, hPW⟩` from `h`. Rewrite `hP` using `[nhds_pi, Filter.mem_pi]`.

Take `⟨I, -, t, ht, hIt⟩` from `hP`. Use `⟨t 0, ht 0, t 1, ht 1, t 2, ht 2, t 3, ht 3, fun y h₁ h₂ h₃ h₄ => hPW (hIt ?_)⟩` and prove the remaining obligations. Rewrite using `[Set.mem_pi]`. Introduce `i _`. Use `fin_cases i`.

Conclude with `h₁`. Conclude with `h₂`. Conclude with `h₃`. Conclude with `h₄`.
-/
private lemma quaternionAlgebra_exists_coord_nhds_subset_of_mem_nhds {k : Type} [CommRing k] [TopologicalSpace k] {a b : k}
    {g : ℍ[k, a, b]} {W : Set ℍ[k, a, b]} (hW : W ∈ 𝓝 g) :
    ∃ N₁ ∈ 𝓝 g.re, ∃ N₂ ∈ 𝓝 g.imI, ∃ N₃ ∈ 𝓝 g.imJ, ∃ N₄ ∈ 𝓝 g.imK,
      ∀ y : ℍ[k, a, b], y.re ∈ N₁ → y.imI ∈ N₂ → y.imJ ∈ N₃ → y.imK ∈ N₄ → y ∈ W := by
  have h : W ∈ Filter.comap _root_.GlobalTheory.QSA.coords (𝓝 (_root_.GlobalTheory.QSA.coords g)) := by
    rw [← nhds_induced]
    exact hW
  obtain ⟨P, hP, hPW⟩ := h
  rw [nhds_pi, Filter.mem_pi] at hP
  obtain ⟨I, -, t, ht, hIt⟩ := hP
  refine ⟨t 0, ht 0, t 1, ht 1, t 2, ht 2, t 3, ht 3, fun y h₁ h₂ h₃ h₄ => hPW (hIt ?_)⟩
  rw [Set.mem_pi]
  intro i _
  fin_cases i
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

open NumberField IsDedekindDomain in
open scoped Quaternion Topology RestrictedProduct in
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
Set `x' : Πʳ i, [R i, A i]_[Filter.principal S]` to `RestrictedProduct.mk (fun i => x i) (Filter.eventually_principal.2 hx)`. Establish `hxx : RestrictedProduct.inclusion R A hS x' = x` using `RestrictedProduct.ext R A fun i => rfl`. Rewrite `hN` using `[← hxx, RestrictedProduct.nhds_eq_map_inclusion hA hS, Filter.mem_map, (RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A) (S := S)).isInducing.nhds_eq_comap, Filter.mem_comap]`. Take `⟨M, hM, hMN⟩` from `hN`. Rewrite `hM` using `[nhds_pi, Filter.mem_pi]`.

Take `⟨I, hI, t, ht, hIt⟩` from `hM`. Use `⟨I, hI, fun i => t i ∩ {z | i ∈ S → z ∈ A i}, fun i => Filter.inter_mem (ht i) ?_, fun i hi z hz => hz.2 hi, fun y hyI hyS => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi : i ∈ S`. Conclude with `Filter.mem_of_superset ((hA i).mem_nhds (hx i hi)) fun z hz _ => hz`. Conclude with `Filter.univ_mem' fun z h => absurd h hi`.

Set `y' : Πʳ i, [R i, A i]_[Filter.principal S]` to `RestrictedProduct.mk (fun i => y i) (Filter.eventually_principal.2 hyS)`. Establish `hy : (⇑y') ∈ I.pi t` using `Set.mem_pi.2 fun i hi => (hyI i hi).1`. Establish `hyN` using `hMN (hIt hy)`. Establish `e : RestrictedProduct.inclusion R A hS y' = y` using `RestrictedProduct.ext R A fun i => rfl`. Rewrite `hyN` using `[Set.mem_preimage, e]`.

Conclude with `hyN`.
-/
private lemma restrictedProduct_exists_finite_box_subset_of_mem_nhds (hA : ∀ i, IsOpen (A i)) {S : Set ι}
    (hS : Filter.cofinite ≤ Filter.principal S) (x : Πʳ i, [R i, A i]) (hx : ∀ i ∈ S, x i ∈ A i)
    {N : Set (Πʳ i, [R i, A i])} (hN : N ∈ 𝓝 x) :
    ∃ I : Set ι, I.Finite ∧ ∃ U : (i : ι) → Set (R i), (∀ i, U i ∈ 𝓝 (x i)) ∧
      (∀ i ∈ S, U i ⊆ A i) ∧
      ∀ y : Πʳ i, [R i, A i], (∀ i ∈ I, y i ∈ U i) → (∀ i ∈ S, y i ∈ A i) → y ∈ N := by
  let x' : Πʳ i, [R i, A i]_[Filter.principal S] :=
    RestrictedProduct.mk (fun i => x i) (Filter.eventually_principal.2 hx)
  have hxx : RestrictedProduct.inclusion R A hS x' = x := RestrictedProduct.ext R A fun i => rfl
  rw [← hxx, RestrictedProduct.nhds_eq_map_inclusion hA hS, Filter.mem_map,
    (RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A) (S := S)).isInducing.nhds_eq_comap,
    Filter.mem_comap] at hN
  obtain ⟨M, hM, hMN⟩ := hN
  rw [nhds_pi, Filter.mem_pi] at hM
  obtain ⟨I, hI, t, ht, hIt⟩ := hM
  refine ⟨I, hI, fun i => t i ∩ {z | i ∈ S → z ∈ A i}, fun i => Filter.inter_mem (ht i) ?_,
    fun i hi z hz => hz.2 hi, fun y hyI hyS => ?_⟩
  · by_cases hi : i ∈ S
    · exact Filter.mem_of_superset ((hA i).mem_nhds (hx i hi)) fun z hz _ => hz
    · exact Filter.univ_mem' fun z h => absurd h hi
  · let y' : Πʳ i, [R i, A i]_[Filter.principal S] :=
      RestrictedProduct.mk (fun i => y i) (Filter.eventually_principal.2 hyS)
    have hy : (⇑y') ∈ I.pi t := Set.mem_pi.2 fun i hi => (hyI i hi).1
    have hyN := hMN (hIt hy)
    have e : RestrictedProduct.inclusion R A hS y' = y := RestrictedProduct.ext R A fun i => rfl
    rw [Set.mem_preimage, e] at hyN
    exact hyN

open NumberField IsDedekindDomain in
open scoped Quaternion Topology RestrictedProduct in
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
The claim follows from `(continuous_apply (0 : Fin 4)).comp (continuous_induced_dom (f := _root_.GlobalTheory.QSA.coords))`.
-/
private lemma continuous_quaternionAlgebra_re {k : Type} [CommRing k] [TopologicalSpace k] {a b : k} :
    Continuous fun w : ℍ[k, a, b] => w.re :=
  (continuous_apply (0 : Fin 4)).comp (continuous_induced_dom (f := _root_.GlobalTheory.QSA.coords))

open NumberField IsDedekindDomain in
open scoped Quaternion Topology RestrictedProduct in
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
The claim follows from `(continuous_apply (1 : Fin 4)).comp (continuous_induced_dom (f := _root_.GlobalTheory.QSA.coords))`.
-/
private lemma continuous_quaternionAlgebra_imI {k : Type} [CommRing k] [TopologicalSpace k] {a b : k} :
    Continuous fun w : ℍ[k, a, b] => w.imI :=
  (continuous_apply (1 : Fin 4)).comp (continuous_induced_dom (f := _root_.GlobalTheory.QSA.coords))

open NumberField IsDedekindDomain in
open scoped Quaternion Topology RestrictedProduct in
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
The claim follows from `(continuous_apply (2 : Fin 4)).comp (continuous_induced_dom (f := _root_.GlobalTheory.QSA.coords))`.
-/
private lemma continuous_quaternionAlgebra_imJ {k : Type} [CommRing k] [TopologicalSpace k] {a b : k} :
    Continuous fun w : ℍ[k, a, b] => w.imJ :=
  (continuous_apply (2 : Fin 4)).comp (continuous_induced_dom (f := _root_.GlobalTheory.QSA.coords))

open NumberField IsDedekindDomain in
open scoped Quaternion Topology RestrictedProduct in
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
The claim follows from `(continuous_apply (3 : Fin 4)).comp (continuous_induced_dom (f := _root_.GlobalTheory.QSA.coords))`.
-/
private lemma continuous_quaternionAlgebra_imK {k : Type} [CommRing k] [TopologicalSpace k] {a b : k} :
    Continuous fun w : ℍ[k, a, b] => w.imK :=
  (continuous_apply (3 : Fin 4)).comp (continuous_induced_dom (f := _root_.GlobalTheory.QSA.coords))

open NumberField IsDedekindDomain in
open scoped Quaternion Topology RestrictedProduct in
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
Set `φ` to `RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (B := fun v => v.adicCompletionIntegers F) (𝓕 := Filter.cofinite) v`. Express the relevant statement in the definitionally equal form `φ (_root_.GlobalTheory.QSA.nrm x) = _`. Simplify using `only [_root_.GlobalTheory.QSA.nrm, map_sub, map_add, map_mul, map_pow]`. Both sides reduce to the same expression.
-/
private lemma nrm_apply_eq_nrm_finAdele_loc {a b : F}
    (x : ℍ[FiniteAdeleRing (𝓞 F) F, algebraMap F (FiniteAdeleRing (𝓞 F) F) a,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) b]) (v : HeightOneSpectrum (𝓞 F)) :
    _root_.GlobalTheory.QSA.nrm x v =
      _root_.GlobalTheory.QSA.nrm (_root_.GlobalTheory.QSA.FinAdele.loc v x) := by
  let φ := RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (B := fun v => v.adicCompletionIntegers F) (𝓕 := Filter.cofinite) v
  change φ (_root_.GlobalTheory.QSA.nrm x) = _
  simp only [_root_.GlobalTheory.QSA.nrm, map_sub, map_add, map_mul, map_pow]
  rfl

open NumberField IsDedekindDomain in
open scoped Quaternion Topology RestrictedProduct in
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} in
variable {F : Type} [Field F] [NumberField F] in

/- English proof (translation)
Introduce `F _ _ a b hloc hint`. Unfold `_root_.GlobalTheory.QSA.TraceOpen`. Introduce `g hg W hW`. Establish `hAopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))` using `fun v => Valued.isOpen_valuationSubring _`. Take `⟨N₁, hN₁, N₂, hN₂, N₃, hN₃, N₄, hN₄, hNW⟩` from `quaternionAlgebra_exists_coord_nhds_subset_of_mem_nhds hW`.

Take `⟨S, hS, hSP⟩` from `Filter.eventually_iff_exists_mem.1 (g.re.2.and (g.imI.2.and (g.imJ.2.and (g.imK.2.and hint))))`. Establish `hS' : Filter.cofinite ≤ Filter.principal S` using `Filter.le_principal_iff.2 hS`. Take `⟨I₁, hI₁, U₁, hU₁, hU₁A, h₁⟩` from `restrictedProduct_exists_finite_box_subset_of_mem_nhds (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hAopen hS' g.re (fun v hv => (hSP v hv).1) hN₁`. Take `⟨I₂, hI₂, U₂, hU₂, hU₂A, h₂⟩` from `restrictedProduct_exists_finite_box_subset_of_mem_nhds (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hAopen hS' g.imI (fun v hv => (hSP v hv).2.1) hN₂`. Take `⟨I₃, hI₃, U₃, hU₃, hU₃A, h₃⟩` from `restrictedProduct_exists_finite_box_subset_of_mem_nhds (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hAopen hS' g.imJ (fun v hv => (hSP v hv).2.2.1) hN₃`.

Take `⟨I₄, hI₄, U₄, hU₄, hU₄A, h₄⟩` from `restrictedProduct_exists_finite_box_subset_of_mem_nhds (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hAopen hS' g.imK (fun v hv => (hSP v hv).2.2.2.1) hN₄`. Set `J : Set (HeightOneSpectrum (𝓞 F))` to `I₁ ∪ I₂ ∪ I₃ ∪ I₄ ∪ Sᶜ`. Establish `hJ : J.Finite` using `(((hI₁.union hI₂).union hI₃).union hI₄).union (Filter.mem_cofinite.1 hS)`. Establish `hWv : ∀ v : HeightOneSpectrum (𝓞 F), (fun w : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b] => w.re) ⁻¹' U₁ v ∩ ((fun w : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b] => w.imI) ⁻¹ …` using `fun v => Filter.inter_mem (continuous_quaternionAlgebra_re.continuousAt.preimage_mem_nhds (hU₁ v)) (Filter.inter_mem (continuous_quaternionAlgebra_imI.continuousAt.preimage_mem_nhds (hU₂ v)) (Filter.inter_mem (continuous_quaternionAlgebra_imJ.continuousAt.preimage_mem_nhds (hU₃ v …`. Establish `hgv : ∀ v : HeightOneSpectrum (𝓞 F), _root_.GlobalTheory.QSA.nrm (_root_.GlobalTheory.QSA.FinAdele.loc v g) = 1`.

Introduce `v`. Rewrite using `[← nrm_apply_eq_nrm_finAdele_loc, hg]`. Both sides reduce to the same expression. Use `choose O hOopen hOne hOu using fun v => hloc v _ (hgv v) _ (hWv v)`. Use `⟨(⋂ v ∈ J, (fun t : FiniteAdeleRing (𝓞 F) F => t v) ⁻¹' O v) ∩ {t | ∀ v, v ∉ J → t v ∈ v.adicCompletionIntegers F}, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `IsOpen.inter (hJ.isOpen_biInter fun v _ => (hOopen v).preimage (RestrictedProduct.continuous_eval v)) ?_` and prove the remaining obligations. Conclude with `RestrictedProduct.isOpen_forall_imp_mem hAopen (p := fun v => v ∉ J)`. Set `t₀ : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]` to `⟨fun v => if v ∈ J then (hOne v).some else 0, Filter.eventually_cofinite.2 (hJ.subset fun v hv => by`. Assume the negation of the conclusion as `hvJ`. Conclude with `hv (by simp only [if_neg hvJ]; exact zero_mem _))⟩`.

Use `⟨t₀, Set.mem_iInter₂.2 fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Use `show (if v ∈ J then (hOne v).some else 0) ∈ O v`. Rewrite using `[if_pos hv]`. Conclude with `(hOne v).some_mem`. Use `show (if v ∈ J then (hOne v).some else 0) ∈ v.adicCompletionIntegers F`.

Rewrite using `[if_neg hv]`. Conclude with `zero_mem _`. Introduce and unpack `t ⟨htJ, htA⟩`. Rewrite `htJ` using `[Set.mem_iInter₂]`. Establish `hu : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b], _root_.GlobalTheory.QSA.nrm u = 1 ∧ u.re = t v ∧ (v ∈ J → u.re ∈ U₁ v ∧ u.imI ∈ U₂ v ∧ u.imJ ∈ U₃ v ∧ u.imK ∈ U₄ v) ∧ (v ∈ S → u.imI ∈ v.adic …`.

Introduce `v`. Distinguish the cases in `hv : v ∈ J`. Take `⟨u, ⟨k₁, k₂, k₃, k₄⟩, hn, hre⟩` from `hOu v (t v) (htJ v hv)`. Conclude with `⟨u, hn, hre, fun _ => ⟨k₁, k₂, k₃, k₄⟩, fun hvS => ⟨hU₂A v hvS k₂, hU₃A v hvS k₃, hU₄A v hvS k₄⟩⟩`. Establish `hvS : v ∈ S`.

Assume the negation of the conclusion as `h`. Conclude with `hv (Set.mem_union_right _ h)`. Take `⟨u, hn, hre, k₂, k₃, k₄⟩` from `(hSP v hvS).2.2.2.2 (t v) (htA v hv)`. Conclude with `⟨u, hn, hre, fun h => absurd h hv, fun _ => ⟨k₂, k₃, k₄⟩⟩`. Use `choose u hun hure huJ huS using hu`.

Establish `htS : ∀ v ∈ S, t v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))`. Introduce `v hv`. Distinguish the cases in `hvJ : v ∈ J`. Rewrite using `[← hure v]`. Conclude with `hU₁A v hv (huJ v hvJ).1`.

Conclude with `htA v hvJ`. Establish `hevS : ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), v ∈ S` using `hS`. Set `yI : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]` to `⟨fun v => (u v).imI, hevS.mono fun v hv => (huS v hv).1⟩`. Set `yJ : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]` to `⟨fun v => (u v).imJ, hevS.mono fun v hv => (huS v hv).2.1⟩`. Set `yK : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]` to `⟨fun v => (u v).imK, hevS.mono fun v hv => (huS v hv).2.2⟩`.

Set `y : ℍ[FiniteAdeleRing (𝓞 F) F, algebraMap F (FiniteAdeleRing (𝓞 F) F) a, algebraMap F (FiniteAdeleRing (𝓞 F) F) b]` to `⟨t, yI, yJ, yK⟩`. Use `⟨y, hNW y ?_ ?_ ?_ ?_, ?_, rfl⟩` and prove the remaining obligations. Use `h₁ t (fun v hv => ?_) htS` and prove the remaining obligations. Establish `k` using `(huJ v (Or.inl (Or.inl (Or.inl (Or.inl hv))))).1`. Rewrite `k` using `[hure v]`.

Conclude with `k`. Conclude with `h₂ yI (fun v hv => (huJ v (Or.inl (Or.inl (Or.inl (Or.inr hv))))).2.1) (fun v hv => (huS v hv).1)`. Conclude with `h₃ yJ (fun v hv => (huJ v (Or.inl (Or.inl (Or.inr hv)))).2.2.1) (fun v hv => (huS v hv).2.1)`. Conclude with `h₄ yK (fun v hv => (huJ v (Or.inl (Or.inr hv))).2.2.2) (fun v hv => (huS v hv).2.2)`. Use `RestrictedProduct.ext _ _ fun v => ?_` and prove the remaining obligations.

Establish `hloc_y : _root_.GlobalTheory.QSA.FinAdele.loc v y = u v` using `QuaternionAlgebra.ext (hure v).symm rfl rfl rfl`. Use `(nrm_apply_eq_nrm_finAdele_loc y v).trans ?_` and prove the remaining obligations. Rewrite using `[hloc_y, hun v]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele : ∀ (F : Type) [Field F] [NumberField F] (a b : F), (∀ v : HeightOneSpectrum (𝓞 F), _root_.GlobalTheory.QSA.TraceOpen (v.adicCompletion F) (algebraMap F (v.adicCompletion F) a) (algebraMap F (v.adicCompletion F) b)) → (∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F, ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b], _root_.GlobalTheory.QSA.nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧ u.imK ∈ v.adicCompletionIntegers F) → _root_.GlobalTheory.QSA.TraceOpen (FiniteAdeleRing (𝓞 F) F) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) (algebraMap F (FiniteAdeleRing (𝓞 F) F) b) := by
  intro F _ _ a b hloc hint
  unfold _root_.GlobalTheory.QSA.TraceOpen
  intro g hg W hW
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  obtain ⟨N₁, hN₁, N₂, hN₂, N₃, hN₃, N₄, hN₄, hNW⟩ := quaternionAlgebra_exists_coord_nhds_subset_of_mem_nhds hW
  obtain ⟨S, hS, hSP⟩ := Filter.eventually_iff_exists_mem.1
    (g.re.2.and (g.imI.2.and (g.imJ.2.and (g.imK.2.and hint))))
  have hS' : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 hS
  obtain ⟨I₁, hI₁, U₁, hU₁, hU₁A, h₁⟩ := restrictedProduct_exists_finite_box_subset_of_mem_nhds
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    hAopen hS' g.re (fun v hv => (hSP v hv).1) hN₁
  obtain ⟨I₂, hI₂, U₂, hU₂, hU₂A, h₂⟩ := restrictedProduct_exists_finite_box_subset_of_mem_nhds
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    hAopen hS' g.imI (fun v hv => (hSP v hv).2.1) hN₂
  obtain ⟨I₃, hI₃, U₃, hU₃, hU₃A, h₃⟩ := restrictedProduct_exists_finite_box_subset_of_mem_nhds
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    hAopen hS' g.imJ (fun v hv => (hSP v hv).2.2.1) hN₃
  obtain ⟨I₄, hI₄, U₄, hU₄, hU₄A, h₄⟩ := restrictedProduct_exists_finite_box_subset_of_mem_nhds
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    hAopen hS' g.imK (fun v hv => (hSP v hv).2.2.2.1) hN₄
  let J : Set (HeightOneSpectrum (𝓞 F)) := I₁ ∪ I₂ ∪ I₃ ∪ I₄ ∪ Sᶜ
  have hJ : J.Finite :=
    (((hI₁.union hI₂).union hI₃).union hI₄).union (Filter.mem_cofinite.1 hS)
  have hWv : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun w : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a,
        algebraMap F (v.adicCompletion F) b] => w.re) ⁻¹' U₁ v ∩
      ((fun w : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a,
        algebraMap F (v.adicCompletion F) b] => w.imI) ⁻¹' U₂ v ∩
      ((fun w : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a,
        algebraMap F (v.adicCompletion F) b] => w.imJ) ⁻¹' U₃ v ∩
      (fun w : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a,
        algebraMap F (v.adicCompletion F) b] => w.imK) ⁻¹' U₄ v)) ∈
        𝓝 (_root_.GlobalTheory.QSA.FinAdele.loc v g) := fun v =>
    Filter.inter_mem (continuous_quaternionAlgebra_re.continuousAt.preimage_mem_nhds (hU₁ v))
      (Filter.inter_mem (continuous_quaternionAlgebra_imI.continuousAt.preimage_mem_nhds (hU₂ v))
        (Filter.inter_mem (continuous_quaternionAlgebra_imJ.continuousAt.preimage_mem_nhds (hU₃ v))
          (continuous_quaternionAlgebra_imK.continuousAt.preimage_mem_nhds (hU₄ v))))
  have hgv : ∀ v : HeightOneSpectrum (𝓞 F),
      _root_.GlobalTheory.QSA.nrm (_root_.GlobalTheory.QSA.FinAdele.loc v g) = 1 := by
    intro v
    rw [← nrm_apply_eq_nrm_finAdele_loc, hg]
    rfl
  choose O hOopen hOne hOu using fun v => hloc v _ (hgv v) _ (hWv v)
  refine ⟨(⋂ v ∈ J, (fun t : FiniteAdeleRing (𝓞 F) F => t v) ⁻¹' O v) ∩
    {t | ∀ v, v ∉ J → t v ∈ v.adicCompletionIntegers F}, ?_, ?_, ?_⟩
  · refine IsOpen.inter (hJ.isOpen_biInter fun v _ =>
      (hOopen v).preimage (RestrictedProduct.continuous_eval v)) ?_
    exact RestrictedProduct.isOpen_forall_imp_mem hAopen (p := fun v => v ∉ J)
  · let t₀ : Πʳ v : HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))] :=
      ⟨fun v => if v ∈ J then (hOne v).some else 0, Filter.eventually_cofinite.2 (hJ.subset
        fun v hv => by
          by_contra hvJ
          exact hv (by simp only [if_neg hvJ]; exact zero_mem _))⟩
    refine ⟨t₀, Set.mem_iInter₂.2 fun v hv => ?_, fun v hv => ?_⟩
    · show (if v ∈ J then (hOne v).some else 0) ∈ O v
      rw [if_pos hv]
      exact (hOne v).some_mem
    · show (if v ∈ J then (hOne v).some else 0) ∈ v.adicCompletionIntegers F
      rw [if_neg hv]
      exact zero_mem _
  · rintro t ⟨htJ, htA⟩
    rw [Set.mem_iInter₂] at htJ
    have hu : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u : ℍ[v.adicCompletion F,
        algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b],
        _root_.GlobalTheory.QSA.nrm u = 1 ∧ u.re = t v ∧
        (v ∈ J → u.re ∈ U₁ v ∧ u.imI ∈ U₂ v ∧ u.imJ ∈ U₃ v ∧ u.imK ∈ U₄ v) ∧
        (v ∈ S → u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧
          u.imK ∈ v.adicCompletionIntegers F) := by
      intro v
      by_cases hv : v ∈ J
      · obtain ⟨u, ⟨k₁, k₂, k₃, k₄⟩, hn, hre⟩ := hOu v (t v) (htJ v hv)
        exact ⟨u, hn, hre, fun _ => ⟨k₁, k₂, k₃, k₄⟩,
          fun hvS => ⟨hU₂A v hvS k₂, hU₃A v hvS k₃, hU₄A v hvS k₄⟩⟩
      · have hvS : v ∈ S := by
          by_contra h
          exact hv (Set.mem_union_right _ h)
        obtain ⟨u, hn, hre, k₂, k₃, k₄⟩ := (hSP v hvS).2.2.2.2 (t v) (htA v hv)
        exact ⟨u, hn, hre, fun h => absurd h hv, fun _ => ⟨k₂, k₃, k₄⟩⟩
    choose u hun hure huJ huS using hu
    have htS : ∀ v ∈ S, t v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      intro v hv
      by_cases hvJ : v ∈ J
      · rw [← hure v]
        exact hU₁A v hv (huJ v hvJ).1
      · exact htA v hvJ
    have hevS : ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), v ∈ S := hS
    let yI : Πʳ v : HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))] :=
      ⟨fun v => (u v).imI, hevS.mono fun v hv => (huS v hv).1⟩
    let yJ : Πʳ v : HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))] :=
      ⟨fun v => (u v).imJ, hevS.mono fun v hv => (huS v hv).2.1⟩
    let yK : Πʳ v : HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))] :=
      ⟨fun v => (u v).imK, hevS.mono fun v hv => (huS v hv).2.2⟩
    let y : ℍ[FiniteAdeleRing (𝓞 F) F, algebraMap F (FiniteAdeleRing (𝓞 F) F) a,
        algebraMap F (FiniteAdeleRing (𝓞 F) F) b] := ⟨t, yI, yJ, yK⟩
    refine ⟨y, hNW y ?_ ?_ ?_ ?_, ?_, rfl⟩
    · refine h₁ t (fun v hv => ?_) htS
      have k := (huJ v (Or.inl (Or.inl (Or.inl (Or.inl hv))))).1
      rw [hure v] at k
      exact k
    · exact h₂ yI (fun v hv => (huJ v (Or.inl (Or.inl (Or.inl (Or.inr hv))))).2.1)
        (fun v hv => (huS v hv).1)
    · exact h₃ yJ (fun v hv => (huJ v (Or.inl (Or.inl (Or.inr hv)))).2.2.1)
        (fun v hv => (huS v hv).2.1)
    · exact h₄ yK (fun v hv => (huJ v (Or.inl (Or.inr hv))).2.2.2)
        (fun v hv => (huS v hv).2.2)
    · refine RestrictedProduct.ext _ _ fun v => ?_
      have hloc_y : _root_.GlobalTheory.QSA.FinAdele.loc v y = u v :=
        QuaternionAlgebra.ext (hure v).symm rfl rfl rfl
      refine (nrm_apply_eq_nrm_finAdele_loc y v).trans ?_
      rw [hloc_y, hun v]
      rfl

end GlobalTheory.QSA.FinAdele
