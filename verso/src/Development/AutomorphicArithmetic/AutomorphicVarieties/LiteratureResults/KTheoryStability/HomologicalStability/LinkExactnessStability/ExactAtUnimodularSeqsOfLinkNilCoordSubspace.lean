import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainExactAtMapIff

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCxLow

noncomputable def emb (R : Type) [CommRing R] (m : ℕ) : (Fin m → R) →ₗ[R] (ℕ →₀ R) :=
  Finsupp.lmapDomain R R Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite R R (Fin m)).symm.toLinearMap

/- English proof (translation)
Simplify using `[emb, Finsupp.mapDomain_apply Fin.val_injective]`.
-/
theorem emb_apply_val {R : Type} [CommRing R] {m : ℕ} (v : Fin m → R) (k : Fin m) :
    emb R m v (k : ℕ) = v k := by
  simp [emb, Finsupp.mapDomain_apply Fin.val_injective]

/- English proof (translation)
Simplify using `only [emb, LinearMap.comp_apply, Finsupp.lmapDomain_apply, LinearEquiv.coe_coe]`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨k, hk⟩`. Establish `hk2` using `k.isLt`. Use linear arithmetic over natural numbers and integers.
-/
theorem emb_apply_of_le {R : Type} [CommRing R] {m : ℕ} (v : Fin m → R) (n : ℕ) (h : m ≤ n) :
    emb R m v n = 0 := by
  simp only [emb, LinearMap.comp_apply, Finsupp.lmapDomain_apply, LinearEquiv.coe_coe]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨k, hk⟩
  have hk2 := k.isLt
  omega

/- English proof (translation)
Introduce `v w hvw`. Use function extensionality and compare the values at `k`. Establish `e` using `congrArg (fun x => x (k : ℕ)) hvw`. Simplify `e` using `only [emb_apply_val]`.
-/
theorem emb_injective (R : Type) [CommRing R] (m : ℕ) : Function.Injective (emb R m) := by
  intro v w hvw
  funext k
  have e := congrArg (fun x => x (k : ℕ)) hvw
  simpa only [emb_apply_val] using e

/- English proof (translation)
Introduce `n h` and use `emb_apply_of_le v n h`.
-/
theorem emb_mem_low {R : Type} [CommRing R] {m : ℕ} (v : Fin m → R) : emb R m v ∈ low R m :=
  fun n h => emb_apply_of_le v n h

/- English proof (translation)
Use extensionality with `n`. Distinguish the cases in `h : n < m`. Establish `e` using `emb_apply_val (fun k : Fin m => x k) ⟨n, h⟩`. Simplify using `using e`. Rewrite using `[emb_apply_of_le _ n (not_lt.mp h)]`.

Conclude with `(hx n (not_lt.mp h)).symm`.
-/
theorem emb_restrict {R : Type} [CommRing R] {m : ℕ} (x : ℕ →₀ R) (hx : x ∈ low R m) :
    emb R m (fun k : Fin m => x k) = x := by
  ext n
  by_cases h : n < m
  · have e := emb_apply_val (fun k : Fin m => x k) ⟨n, h⟩
    simpa using e
  · rw [emb_apply_of_le _ n (not_lt.mp h)]
    exact (hx n (not_lt.mp h)).symm

/- English proof (translation)
Simplify using `[dotProduct, emb_apply_val]`.
-/
theorem form_emb {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (v : Fin m → R) :
    (∑ k : Fin m, g k • Finsupp.lapply (R := R) (M := R) (k : ℕ)) (emb R m v) = g ⬝ᵥ v := by
  simp [dotProduct, emb_apply_val]

/- English proof (translation)
Establish `hs : ∀ k, (Pi.single k (v k) : Fin m → R) = v k • (Pi.single k 1 : Fin m → R)`. Introduce `k`. Use extensionality with `j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hj]`. Use `conv_rhs => rw [← Finset.univ_sum_single v]`. Simplify using `only [map_sum, hs, map_smul, smul_eq_mul, dotProduct]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations.

Introduce `k _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem emb_form {R : Type} [CommRing R] {m : ℕ} (f : (ℕ →₀ R) →ₗ[R] R) (v : Fin m → R) :
    (fun k => f (emb R m (Pi.single k 1))) ⬝ᵥ v = f (emb R m v) := by
  have hs : ∀ k, (Pi.single k (v k) : Fin m → R) = v k • (Pi.single k 1 : Fin m → R) := by
    intro k
    ext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [Pi.single_apply, hj]
  conv_rhs => rw [← Finset.univ_sum_single v]
  simp only [map_sum, hs, map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

/- English proof (translation)
Use extensionality with `w`. Simplify using `only [linkIn, Set.mem_setOf_eq, List.nil_append, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hw, f, hf⟩`. Use `⟨w.map (fun x (k : Fin m) => x k), ⟨fun i k => f (Fin.cast (by simp) i) (emb R m (Pi.single k 1)), ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `i j`. Simplify using `only [List.get_eq_getElem, List.getElem_map]`. Rewrite using `[emb_form, emb_restrict _ (hw _ (List.getElem_mem _))]`. Establish `e` using `hf (Fin.cast (by simp) i) (Fin.cast (by simp) j)`. Simplify `e` using `[List.get_eq_getElem, Fin.ext_iff]`.

Rewrite using `[List.map_map]`. Use `(List.map_congr_left ?_).trans (List.map_id w)` and prove the remaining obligations. Introduce `x hx`. Conclude with `emb_restrict x (hw x hx)`. Introduce and unpack `⟨u, ⟨g, hg⟩, rfl⟩`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, _, rfl⟩` from `List.mem_map.mp hx`. Conclude with `emb_mem_low y`. Use `⟨fun i => ∑ k : Fin m, g (Fin.cast (by simp) i) k • Finsupp.lapply (R := R) (M := R) (k : ℕ), ?_⟩` and prove the remaining obligations.

Introduce `i j`. Simplify using `only [List.get_eq_getElem, List.getElem_map]`. Rewrite using `[form_emb]`. Establish `e` using `hg (Fin.cast (by simp) i) (Fin.cast (by simp) j)`. Simplify `e` using `[List.get_eq_getElem, Fin.ext_iff]`.
-/
theorem link_eq (R : Type) [CommRing R] (m : ℕ) :
    linkIn (uniM R (ℕ →₀ R)) (low R m) [] = List.map (emb R m) '' uniSeq R m := by
  ext w
  simp only [linkIn, Set.mem_setOf_eq, List.nil_append, Set.mem_image]
  constructor
  · rintro ⟨hw, f, hf⟩
    refine ⟨w.map (fun x (k : Fin m) => x k), ⟨fun i k => f (Fin.cast (by simp) i) (emb R m (Pi.single k 1)), ?_⟩, ?_⟩
    · intro i j
      simp only [List.get_eq_getElem, List.getElem_map]
      rw [emb_form, emb_restrict _ (hw _ (List.getElem_mem _))]
      have e := hf (Fin.cast (by simp) i) (Fin.cast (by simp) j)
      simpa [List.get_eq_getElem, Fin.ext_iff] using e
    · rw [List.map_map]
      refine (List.map_congr_left ?_).trans (List.map_id w)
      intro x hx
      exact emb_restrict x (hw x hx)
  · rintro ⟨u, ⟨g, hg⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact emb_mem_low y
    · refine ⟨fun i => ∑ k : Fin m, g (Fin.cast (by simp) i) k • Finsupp.lapply (R := R) (M := R) (k : ℕ), ?_⟩
      intro i j
      simp only [List.get_eq_getElem, List.getElem_map]
      rw [form_emb]
      have e := hg (Fin.cast (by simp) i) (Fin.cast (by simp) j)
      simpa [List.get_eq_getElem, Fin.ext_iff] using e

end GlobalTheory.SeqCxLow

/- English proof (translation)
Establish `hM : Function.Injective (List.map e)` using `List.map_injective_iff.mpr he`. Establish `comm : ∀ c, bd U (Finsupp.mapDomain (List.map e) c) = Finsupp.mapDomain (List.map e) (bd V c)`. Introduce `c`. Establish `E : (bd U).comp (Finsupp.lmapDomain ℤ ℤ (List.map e)) = (Finsupp.lmapDomain ℤ ℤ (List.map e)).comp (bd V)`. Apply `Finsupp.lhom_ext'` to reduce the goal to its premises.

Introduce `l`. Apply `LinearMap.ext_ring` to reduce the goal to its premises. Simplify using `[bd, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_smul, Finsupp.mapDomain_single, List.eraseIdx_map]`. Conclude with `LinearMap.congr_fun E c`. Introduce `c hc hbc`.

Establish `hc' : Finsupp.mapDomain (List.map e) c ∈ chains (List.map e '' F) q`. Rewrite `hc`, the goal using `[chains, Finsupp.mem_supported]`. Introduce `z hz`. Take `⟨l, hl, rfl⟩` from `Finset.mem_image.mp (Finsupp.mapDomain_support (Finset.mem_coe.mp hz))`. Establish `hl'` using `hc (Finset.mem_coe.mpr hl)`.

Conclude with `⟨⟨l, hl'.1, rfl⟩, by simp [hl'.2]⟩`. Take `⟨b', hb', hbb⟩` from `h _ hc' (by rw [comm, hbc, Finsupp.mapDomain_zero])`. Rewrite `hb'` using `[chains, Finsupp.mem_supported]`. Establish `hrange : ↑b'.support ⊆ Set.range (List.map e)`. Introduce `z hz`.

Take `⟨⟨l, _, rfl⟩, _⟩` from `hb' hz`. Conclude with `⟨l, rfl⟩`. Use `⟨Finsupp.comapDomain (List.map e) b' hM.injOn, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[chains, Finsupp.mem_supported]`. Introduce `l hl`.

Rewrite `hl` using `[Finset.mem_coe, Finsupp.comapDomain_support, Finset.mem_preimage]`. Take `⟨⟨l', hl'F, hl'e⟩, hlen⟩` from `hb' (Finset.mem_coe.mpr hl)`. Establish `hll` using `hM hl'e`. Substitute `hll` using the available equality. Conclude with `⟨hl'F, by simpa using hlen⟩`.

Apply `Finsupp.mapDomain_injective hM` to reduce the goal to its premises. Rewrite using `[← comm, Finsupp.mapDomain_comapDomain (List.map e) hM b' hrange, hbb]`.
-/
private theorem exactAt_of_exactAt_image_injective {V U : Type} (e : V → U) (he : Function.Injective e)
    (F : Set (List V)) (q : ℕ) (h : ExactAt (List.map e '' F) q) : ExactAt F q := by
  classical
  have hM : Function.Injective (List.map e) := List.map_injective_iff.mpr he
  have comm : ∀ c, bd U (Finsupp.mapDomain (List.map e) c) = Finsupp.mapDomain (List.map e) (bd V c) := by
    intro c
    have E : (bd U).comp (Finsupp.lmapDomain ℤ ℤ (List.map e)) = (Finsupp.lmapDomain ℤ ℤ (List.map e)).comp (bd V) := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [bd, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_smul, Finsupp.mapDomain_single, List.eraseIdx_map]
    exact LinearMap.congr_fun E c
  intro c hc hbc
  have hc' : Finsupp.mapDomain (List.map e) c ∈ chains (List.map e '' F) q := by
    rw [chains, Finsupp.mem_supported] at hc ⊢
    intro z hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finset.mem_coe.mp hz))
    have hl' := hc (Finset.mem_coe.mpr hl)
    exact ⟨⟨l, hl'.1, rfl⟩, by simp [hl'.2]⟩
  obtain ⟨b', hb', hbb⟩ := h _ hc' (by rw [comm, hbc, Finsupp.mapDomain_zero])
  rw [chains, Finsupp.mem_supported] at hb'
  have hrange : ↑b'.support ⊆ Set.range (List.map e) := by
    intro z hz
    obtain ⟨⟨l, _, rfl⟩, _⟩ := hb' hz
    exact ⟨l, rfl⟩
  refine ⟨Finsupp.comapDomain (List.map e) b' hM.injOn, ?_, ?_⟩
  · rw [chains, Finsupp.mem_supported]
    intro l hl
    rw [Finset.mem_coe, Finsupp.comapDomain_support, Finset.mem_preimage] at hl
    obtain ⟨⟨l', hl'F, hl'e⟩, hlen⟩ := hb' (Finset.mem_coe.mpr hl)
    have hll := hM hl'e
    subst hll
    exact ⟨hl'F, by simpa using hlen⟩
  · apply Finsupp.mapDomain_injective hM
    rw [← comm, Finsupp.mapDomain_comapDomain (List.map e) hM b' hrange, hbb]

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Introduce `R _ m q h`. Rewrite `h` using `[GlobalTheory.SeqCxLow.link_eq]`. Conclude with `exactAt_of_exactAt_image_injective _ (GlobalTheory.SeqCxLow.emb_injective R m) _ _ h`.
-/
theorem _root_.GlobalTheory.T.exactAt_unimodularSeqs_of_link_nil_coordSubspace : ∀ (R : Type) [CommRing R] (m q : ℕ), ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R m) []) q → ExactAt (uniSeq R m) q := by
  intro R _ m q h
  rw [GlobalTheory.SeqCxLow.link_eq] at h
  exact exactAt_of_exactAt_image_injective _ (GlobalTheory.SeqCxLow.emb_injective R m) _ _ h
end
