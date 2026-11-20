import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AltDoubleSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.BdMem

open CategoryTheory UpperTheory.V.KH

private noncomputable abbrev UpperTheory.V.KH.tupJ {A : Type} (s : Set A) : (s →₀ ℤ) →ₗ[ℤ] (A →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (Subtype.val : s → A)

/- English proof (translation)
The claim follows from `Finsupp.mapDomain_injective Subtype.val_injective`.
-/
private theorem UpperTheory.V.KH.tupJ_inj {A : Type} (s : Set A) : Function.Injective (tupJ s) :=
  Finsupp.mapDomain_injective Subtype.val_injective

/- English proof (translation)
Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `single x c`.

Rewrite using `[Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]`. Conclude with `Finsupp.single_mem_supported ℤ _ x.2`.
-/
private theorem UpperTheory.V.KH.tupJ_mem {A : Type} (s : Set A) (c : s →₀ ℤ) :
    tupJ s c ∈ Finsupp.supported ℤ ℤ s := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | single x c =>
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact Finsupp.single_mem_supported ℤ _ x.2

/- English proof (translation)
Establish `: Finsupp.supported ℤ ℤ s ≤ LinearMap.range (tupJ s)`. Rewrite using `[Finsupp.supported_eq_span_single, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨Finsupp.single ⟨x, hx⟩ 1, by simp [Finsupp.lmapDomain_apply]⟩`. Conclude with `this hb`.
-/
private theorem UpperTheory.V.KH.tupJ_surj {A : Type} (s : Set A) (b : A →₀ ℤ)
    (hb : b ∈ Finsupp.supported ℤ ℤ s) : ∃ c, tupJ s c = b := by
  have : Finsupp.supported ℤ ℤ s ≤ LinearMap.range (tupJ s) := by
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨Finsupp.single ⟨x, hx⟩ 1, by simp [Finsupp.lmapDomain_apply]⟩
  exact this hb

/- English proof (translation)
Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single x c`. Rewrite using `[faceD_single, map_sum, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, UpperTheory.V.ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, smul_comm c, Finsupp.smul_single_one]`.
-/
private theorem UpperTheory.V.KH.tupJ_faceD {I : Type} (S : ∀ n, Set (Fin n → I))
    (hF : UpperTheory.V.ConeExtensionAcyclic.FaceClosed S) (n : ℕ) (c : S (n + 1) →₀ ℤ) :
    tupJ (S n) (faceD (fun (i : Fin (n + 1)) (t : S (n + 1)) =>
      (⟨t.1 ∘ i.succAbove, hF n t.1 t.2 i⟩ : S n)) c) =
      UpperTheory.V.ConeExtensionAcyclic.bd I n (tupJ (S (n + 1)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single x c =>
    rw [faceD_single, map_sum, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      UpperTheory.V.ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, smul_comm c,
      Finsupp.smul_single_one]

/- English proof (translation)
Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb, Finsupp.single_add]`. Consider the case `single x c`. Rewrite using `[Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, UpperTheory.V.ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, aug_single]`.

Rewrite using `[Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_smul, Finsupp.smul_single_one]`. Use `congr 1`. Conclude with `Subsingleton.elim _ _`.
-/
private theorem UpperTheory.V.KH.bd_zero_tupJ {I : Type} (s : Set (Fin (0 + 1) → I)) (c : s →₀ ℤ) :
    UpperTheory.V.ConeExtensionAcyclic.bd I 0 (tupJ s c) = Finsupp.single default (aug s c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, Finsupp.single_add]
  | single x c =>
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      UpperTheory.V.ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, aug_single]
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_smul,
      Finsupp.smul_single_one]
    congr 1
    exact Subsingleton.elim _ _

/- English proof (translation)
Introduce `I S hF h0 hA m`. Take `⟨t0, ht0⟩` from `h0`. Establish `hdef : (default : Fin 0 → I) ∈ S 0`. Rewrite using `[Subsingleton.elim (default : Fin 0 → I) t0]` and apply the resulting hypothesis. Use `⟨fun z => ?_, fun c => ⟨fun hc => ?_, ?_⟩, fun p _ c => ⟨fun hc => ?_, ?_⟩⟩` and prove the remaining obligations.

Take `⟨b, hb, hbz⟩` from `hA.1 (Finsupp.single default z) (Finsupp.single_mem_supported ℤ _ hdef)`. Take `⟨c, rfl⟩` from `tupJ_surj _ b hb`. Conclude with `⟨c, Finsupp.single_injective _ ((bd_zero_tupJ (S (0 + 1)) c).symm.trans hbz)⟩`. Take `⟨b, hb, hbz⟩` from `hA.2 0 (tupJ _ c) (tupJ_mem _ c) (by`. Rewrite using `[bd_zero_tupJ, hc, Finsupp.single_zero])`.

Take `⟨d, rfl⟩` from `tupJ_surj _ b hb`. Conclude with `⟨d, tupJ_inj _ ((tupJ_faceD S hF (0 + 1) d).trans hbz)⟩`. Introduce and unpack `⟨d, rfl⟩`. Apply `Finsupp.single_injective (default : Fin 0 → I)` to reduce the goal to its premises. Establish `h1` using `bd_zero_tupJ (S (0 + 1)) (faceD (fun (i : Fin (0 + 1 + 1)) (t : S (0 + 1 + 1)) => (⟨t.1 ∘ i.succAbove, hF (0 + 1) t.1 t.2 i⟩ : S (0 + 1))) d)`.

Rewrite `h1` using `[tupJ_faceD S hF (0 + 1) d, UpperTheory.V.ConeExtensionAcyclic.bd_bd]`. Conclude with `h1.symm.trans (Finsupp.single_zero _).symm`. Take `⟨b, hb, hbz⟩` from `hA.2 (p + 1) (tupJ _ c) (tupJ_mem _ c) (by`. Rewrite using `[← tupJ_faceD S hF (p + 1) c]`. Conclude with `(congrArg (tupJ (S (p + 1))) hc).trans (map_zero _))`.

Take `⟨d, rfl⟩` from `tupJ_surj _ b hb`. Conclude with `⟨d, tupJ_inj _ ((tupJ_faceD S hF (p + 1 + 1) d).trans hbz)⟩`. Introduce and unpack `⟨d, rfl⟩`. Apply `tupJ_inj (S (p + 1))` to reduce the goal to its premises. Use `(tupJ_faceD S hF (p + 1) _).trans ?_` and prove the remaining obligations.

Use `(congrArg (UpperTheory.V.ConeExtensionAcyclic.bd I (p + 1)) (tupJ_faceD S hF (p + 1 + 1) d)).trans ?_` and prove the remaining obligations. Rewrite using `[UpperTheory.V.ConeExtensionAcyclic.bd_bd, map_zero]`.
-/
theorem UpperTheory.V.KH.tupExact :
    ∀ (I : Type) (S : ∀ n, Set (Fin n → I)) (hF : UpperTheory.V.ConeExtensionAcyclic.FaceClosed S), (S 0).Nonempty →
      UpperTheory.V.ConeExtensionAcyclic.Acyc S → ∀ m : ℕ,
      FaceExactTo (fun p => S (p + 1))
        (fun p i t => ⟨t.1 ∘ i.succAbove, hF (p + 1) t.1 t.2 i⟩) m := by
  intro I S hF h0 hA m
  obtain ⟨t0, ht0⟩ := h0
  have hdef : (default : Fin 0 → I) ∈ S 0 := by
    rwa [Subsingleton.elim (default : Fin 0 → I) t0]
  refine ⟨fun z => ?_, fun c => ⟨fun hc => ?_, ?_⟩, fun p _ c => ⟨fun hc => ?_, ?_⟩⟩
  · obtain ⟨b, hb, hbz⟩ := hA.1 (Finsupp.single default z) (Finsupp.single_mem_supported ℤ _ hdef)
    obtain ⟨c, rfl⟩ := tupJ_surj _ b hb
    exact ⟨c, Finsupp.single_injective _ ((bd_zero_tupJ (S (0 + 1)) c).symm.trans hbz)⟩
  · obtain ⟨b, hb, hbz⟩ := hA.2 0 (tupJ _ c) (tupJ_mem _ c) (by
      rw [bd_zero_tupJ, hc, Finsupp.single_zero])
    obtain ⟨d, rfl⟩ := tupJ_surj _ b hb
    exact ⟨d, tupJ_inj _ ((tupJ_faceD S hF (0 + 1) d).trans hbz)⟩
  · rintro ⟨d, rfl⟩
    apply Finsupp.single_injective (default : Fin 0 → I)
    have h1 := bd_zero_tupJ (S (0 + 1)) (faceD (fun (i : Fin (0 + 1 + 1)) (t : S (0 + 1 + 1)) =>
      (⟨t.1 ∘ i.succAbove, hF (0 + 1) t.1 t.2 i⟩ : S (0 + 1))) d)
    rw [tupJ_faceD S hF (0 + 1) d, UpperTheory.V.ConeExtensionAcyclic.bd_bd] at h1
    exact h1.symm.trans (Finsupp.single_zero _).symm
  · obtain ⟨b, hb, hbz⟩ := hA.2 (p + 1) (tupJ _ c) (tupJ_mem _ c) (by
      rw [← tupJ_faceD S hF (p + 1) c]
      exact (congrArg (tupJ (S (p + 1))) hc).trans (map_zero _))
    obtain ⟨d, rfl⟩ := tupJ_surj _ b hb
    exact ⟨d, tupJ_inj _ ((tupJ_faceD S hF (p + 1 + 1) d).trans hbz)⟩
  · rintro ⟨d, rfl⟩
    apply tupJ_inj (S (p + 1))
    refine (tupJ_faceD S hF (p + 1) _).trans ?_
    refine (congrArg (UpperTheory.V.ConeExtensionAcyclic.bd I (p + 1)) (tupJ_faceD S hF (p + 1 + 1) d)).trans ?_
    rw [UpperTheory.V.ConeExtensionAcyclic.bd_bd, map_zero]
