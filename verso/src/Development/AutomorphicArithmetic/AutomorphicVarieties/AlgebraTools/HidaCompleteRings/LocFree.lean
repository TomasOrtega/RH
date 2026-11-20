import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocIdem
open IsLocalRing UpperTheory.V.Hi

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro y hy`. Simplify using `using hy`. Consider the case `succ n ih => intro y hy`. Rewrite using `[pow_succ', Module.End.mul_apply]`.

Conclude with `h _ (ih y hy)`.
-/
private theorem pres_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    (T : Module.End A M) (h : ∀ y ∈ N, T y ∈ N) (n : ℕ) : ∀ y ∈ N, (T ^ n) y ∈ N := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact h _ (ih y hy)

/- English proof (translation)
Introduce `y hy`. Use `Submodule.smul_induction_on hy (fun r hr n hn => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul hr (h n hn)`. Rewrite using `[map_add]`.

Conclude with `add_mem hx hy`.
-/
private theorem pres_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    (I : Ideal A) (T : Module.End A M) (h : ∀ y ∈ N, T y ∈ N) : ∀ y ∈ I • N, T y ∈ I • N := by
  intro y hy
  refine Submodule.smul_induction_on hy (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr (h n hn)
  · rw [map_add]; exact add_mem hx hy

/- English proof (translation)
Introduce `y hy`. Rewrite using `[LinearMap.sub_apply, Module.algebraMap_end_apply]`. Conclude with `sub_mem (h y hy) (N.smul_mem c hy)`.
-/
private theorem pres_sub {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    (T : Module.End A M) (c : A) (h : ∀ y ∈ N, T y ∈ N) :
    ∀ y ∈ N, (T - algebraMap A (Module.End A M) c) y ∈ N := by
  intro y hy
  rw [LinearMap.sub_apply, Module.algebraMap_end_apply]
  exact sub_mem (h y hy) (N.smul_mem c hy)

/- English proof (translation)
Introduce `A M ι _ _ _ _ Y _ op a h`. Take `⟨e, -, he, hmem, hcomm⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A M ι Y op a h`. Establish `hLY : locPart Y op a ≤ Y` using `inf_le_left`. Establish `hee : ∀ y : Y, e (e y) = e y` using `fun y => by`. Rewrite using `[← Module.End.mul_apply, he.eq]`.

Establish `heL : ∀ y : Y, (e y : M) ∈ locPart Y op a` using `fun y => (hmem _).2 (hee y)`. Establish `hc : ∀ j (y : Y), e ⟨op j y, h.1 j y y.2⟩ = ⟨op j (e y), h.1 j _ (e y).2⟩`. Introduce `j y`. Use `hcomm ((op j).restrict (h.1 j)) (fun i t ht => by` as an intermediate fact. Use extensionality with `z`.

Establish `h1 : ∀ w : Y, (t w : M) = op i w` using `ht`. Simplify using `only [Module.End.mul_apply, h1, LinearMap.restrict_coe_apply]`. Conclude with `h.2 j i z z.2)`. Conclude with `(LinearMap.congr_fun this y).symm`. Establish `hst : ∀ i, ∀ y ∈ locPart Y op a, op i y ∈ locPart Y op a`.

Introduce `i y hy`. Establish `h1` using `(hmem ⟨y, hLY hy⟩).1 hy`. Use `(hmem ⟨op i y, h.1 i y (hLY hy)⟩).2 ?_` and prove the remaining obligations. Establish `h2` using `hc i ⟨y, hLY hy⟩`. Rewrite using `[h2]`.

Simplify using `only [h1]`. Set `E : Y →ₗ[A] locPart Y op a` to `LinearMap.codRestrict _ (Y.subtype ∘ₗ e) heL`. Establish `hE : E ∘ₗ Submodule.inclusion hLY = LinearMap.id`. Use extensionality with `x`. Conclude with `congrArg (fun w : Y => (w : M)) ((hmem ⟨x, hLY x.2⟩).1 x.2)`.

Establish `hfin : Module.Finite A (locPart Y op a)` using `Module.Finite.of_surjective E fun x => ⟨_, LinearMap.congr_fun hE x⟩`. Establish `hkey : ∀ (I : Ideal A), ∀ w ∈ locPart Y op a, w ∈ I • Y → w ∈ I • locPart Y op a`. Introduce `I w hw hw'`. Establish `h0 : ∀ y ∈ I • (⊤ : Submodule A Y), (e y : M) ∈ I • locPart Y op a`. Introduce `y hy`.

Use `Submodule.smul_induction_on hy (fun r hr n _ => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul hr (heL n)`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.

Establish `h1` using `h0 ⟨w, hLY hw⟩ ((Submodule.mem_smul_top_iff I Y _).2 hw')`. Rewrite `h1` using `[(hmem ⟨w, hLY hw⟩).1 hw]`. Then use the resulting hypothesis. Use `⟨⟨hst, fun i j y hy => h.2 i j y (hLY hy)⟩, ?_, hfin, ?_, fun hP => ?_⟩` and prove the remaining obligations. Use `le_antisymm inf_le_left fun x hx => ⟨hx, ?_⟩` and prove the remaining obligations. Establish `hx2` using `hx.2`.

Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf] at hx2 ⊢`. Introduce `i k`. Establish `hmono : Monotone fun n : ℕ => (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A (Module.End A M) (a i)) ^ n)`. Use `monotone_nat_of_le_succ fun n y hy => ?_` and prove the remaining obligations. Rewrite `hy`, the goal using `[Submodule.mem_comap]`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `pres_smul Y _ _ (pres_sub Y _ _ (h.1 i)) _ hy`. Take `⟨n, hn⟩` from `(Submodule.mem_iSup_of_directed _ hmono.directed_le).1 (hx2 i k)`. Use `Submodule.mem_iSup_of_mem n ?_` and prove the remaining obligations. Conclude with `hkey _ _ (pres_pow _ _ (pres_sub _ _ _ (hst i)) n x hx) hn`.

Use `⟨(LinearMap.ker e).map Y.subtype, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce and unpack `x hx ⟨y, hy, rfl⟩`. Establish `h1` using `(hmem y).1 hx`. Establish `h2 : e y = 0` using `hy`.

Rewrite using `[← h1, h2, map_zero]`. Use `le_antisymm (sup_le hLY (Submodule.map_subtype_le _ _)) fun x hx => ?_` and prove the remaining obligations. Establish `: x = (e ⟨x, hx⟩ : M) + Y.subtype (⟨x, hx⟩ - e ⟨x, hx⟩)` using `by simp`. Rewrite using `[this]`. Use `Submodule.add_mem_sup (heL _) ⟨_, ?_, rfl⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `e _ = 0`. Rewrite using `[map_sub, hee, sub_self]`. Introduce and unpack `i x ⟨y, hy, rfl⟩`. Establish `h2 : e y = 0` using `hy`. Use `⟨⟨op i y, h.1 i y y.2⟩, ?_, rfl⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `e _ = 0`. Rewrite using `[hc]`. Simplify using `[h2]`. Use `haveI : Module.Projective A (locPart Y op a) := Module.Projective.of_split _ _ hE`. Conclude with `Module.free_of_flat_of_isLocalRing`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locFree :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → CommOn (locPart Y op a) op ∧ locPart (locPart Y op a) op a = locPart Y op a ∧ Module.Finite A (locPart Y op a) ∧ (∃ Z : Submodule A M, Disjoint (locPart Y op a) Z ∧ locPart Y op a ⊔ Z = Y ∧ ∀ i, ∀ z ∈ Z, op i z ∈ Z) ∧ (Module.Projective A Y → Module.Free A (locPart Y op a)) := by
  intro A M ι _ _ _ _ Y _ op a h
  obtain ⟨e, -, he, hmem, hcomm⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A M ι Y op a h
  have hLY : locPart Y op a ≤ Y := inf_le_left
  have hee : ∀ y : Y, e (e y) = e y := fun y => by
    rw [← Module.End.mul_apply, he.eq]
  have heL : ∀ y : Y, (e y : M) ∈ locPart Y op a := fun y => (hmem _).2 (hee y)
  have hc : ∀ j (y : Y), e ⟨op j y, h.1 j y y.2⟩ = ⟨op j (e y), h.1 j _ (e y).2⟩ := by
    intro j y
    have := hcomm ((op j).restrict (h.1 j)) (fun i t ht => by
      ext z
      have h1 : ∀ w : Y, (t w : M) = op i w := ht
      simp only [Module.End.mul_apply, h1, LinearMap.restrict_coe_apply]
      exact h.2 j i z z.2)
    exact (LinearMap.congr_fun this y).symm
  have hst : ∀ i, ∀ y ∈ locPart Y op a, op i y ∈ locPart Y op a := by
    intro i y hy
    have h1 := (hmem ⟨y, hLY hy⟩).1 hy
    refine (hmem ⟨op i y, h.1 i y (hLY hy)⟩).2 ?_
    have h2 := hc i ⟨y, hLY hy⟩
    rw [h2]
    simp only [h1]
  let E : Y →ₗ[A] locPart Y op a := LinearMap.codRestrict _ (Y.subtype ∘ₗ e) heL
  have hE : E ∘ₗ Submodule.inclusion hLY = LinearMap.id := by
    ext x
    exact congrArg (fun w : Y => (w : M)) ((hmem ⟨x, hLY x.2⟩).1 x.2)
  have hfin : Module.Finite A (locPart Y op a) :=
    Module.Finite.of_surjective E fun x => ⟨_, LinearMap.congr_fun hE x⟩
  have hkey : ∀ (I : Ideal A), ∀ w ∈ locPart Y op a, w ∈ I • Y → w ∈ I • locPart Y op a := by
    intro I w hw hw'
    have h0 : ∀ y ∈ I • (⊤ : Submodule A Y), (e y : M) ∈ I • locPart Y op a := by
      intro y hy
      refine Submodule.smul_induction_on hy (fun r hr n _ => ?_) (fun x y hx hy => ?_)
      · rw [map_smul]; exact Submodule.smul_mem_smul hr (heL n)
      · rw [map_add]; exact add_mem hx hy
    have h1 := h0 ⟨w, hLY hw⟩ ((Submodule.mem_smul_top_iff I Y _).2 hw')
    rwa [(hmem ⟨w, hLY hw⟩).1 hw] at h1
  refine ⟨⟨hst, fun i j y hy => h.2 i j y (hLY hy)⟩, ?_, hfin, ?_, fun hP => ?_⟩
  · refine le_antisymm inf_le_left fun x hx => ⟨hx, ?_⟩
    have hx2 := hx.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf] at hx2 ⊢
    intro i k
    have hmono : Monotone fun n : ℕ =>
        (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A (Module.End A M) (a i)) ^ n) := by
      refine monotone_nat_of_le_succ fun n y hy => ?_
      rw [Submodule.mem_comap] at hy ⊢
      rw [pow_succ', Module.End.mul_apply]
      exact pres_smul Y _ _ (pres_sub Y _ _ (h.1 i)) _ hy
    obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 (hx2 i k)
    refine Submodule.mem_iSup_of_mem n ?_
    exact hkey _ _ (pres_pow _ _ (pres_sub _ _ _ (hst i)) n x hx) hn
  · refine ⟨(LinearMap.ker e).map Y.subtype, ?_, ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      rintro x hx ⟨y, hy, rfl⟩
      have h1 := (hmem y).1 hx
      have h2 : e y = 0 := hy
      rw [← h1, h2, map_zero]
    · refine le_antisymm (sup_le hLY (Submodule.map_subtype_le _ _)) fun x hx => ?_
      have : x = (e ⟨x, hx⟩ : M) + Y.subtype (⟨x, hx⟩ - e ⟨x, hx⟩) := by simp
      rw [this]
      refine Submodule.add_mem_sup (heL _) ⟨_, ?_, rfl⟩
      change e _ = 0
      rw [map_sub, hee, sub_self]
    · rintro i x ⟨y, hy, rfl⟩
      have h2 : e y = 0 := hy
      refine ⟨⟨op i y, h.1 i y y.2⟩, ?_, rfl⟩
      change e _ = 0
      rw [hc]
      simp [h2]
  · haveI : Module.Projective A (locPart Y op a) := Module.Projective.of_split _ _ hE
    exact Module.free_of_flat_of_isLocalRing
