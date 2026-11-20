import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL

namespace PositivityTheory.Rg.Cz

namespace SpecA

variable {n : ℕ}

def Kl {V : Type} [AddCommGroup V] [Module ℂ V] (X : Module.End ℂ V) (s : ℂ) : Prop :=
  ∃ L : List ℕ, (L.map fun r : ℕ => X - algebraMap ℂ _ (s + r)).prod = 0

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil`. Use extensionality with `v`. Simplify using the standard rewrite rules. Consider the case `cons r L ih`.

Establish `key : Φ ∘ₗ (A - algebraMap ℂ _ (g r)) = (B - algebraMap ℂ _ (g r)) ∘ₗ Φ`. Use extensionality with `v`. Establish `hv` using `LinearMap.congr_fun h v`. Simplify using `only [LinearMap.comp_apply] at hv`. Simplify using `[hv]`.

Simplify using `only [List.map_cons, List.prod_cons]`. Rewrite using `[Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, key, LinearMap.comp_assoc, ih, LinearMap.comp_assoc]`.
-/
theorem prodL_nat {ι V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : Φ ∘ₗ A = B ∘ₗ Φ) (g : ι → ℂ) (L : List ι) :
    Φ ∘ₗ (L.map fun r => A - algebraMap ℂ _ (g r)).prod = (L.map fun r => B - algebraMap ℂ _ (g r)).prod ∘ₗ Φ := by
  induction L with
  | nil =>
    ext v
    simp
  | cons r L ih =>
    have key : Φ ∘ₗ (A - algebraMap ℂ _ (g r)) = (B - algebraMap ℂ _ (g r)) ∘ₗ Φ := by
      ext v
      have hv := LinearMap.congr_fun h v
      simp only [LinearMap.comp_apply] at hv
      simp [hv]
    simp only [List.map_cons, List.prod_cons]
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, key,
      LinearMap.comp_assoc, ih, LinearMap.comp_assoc]

/- English proof (translation)
Take `⟨L, hL⟩` from `hB`. Use `⟨L, ?_⟩` and prove the remaining obligations. Establish `hP` using `prodL_nat Φ A B h (fun r : ℕ => s + (r : ℂ)) L`. Rewrite `hP` using `[hL, LinearMap.zero_comp]`. Use extensionality with `v`.

Apply `hΦ` to reduce the goal to its premises. Rewrite using `[LinearMap.zero_apply, map_zero]`. Simplify using `using LinearMap.congr_fun hP v`.
-/
theorem Kl_nat {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) (hΦ : Function.Injective Φ) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : Φ ∘ₗ A = B ∘ₗ Φ)
    (s : ℂ) (hB : Kl B s) : Kl A s := by
  obtain ⟨L, hL⟩ := hB
  refine ⟨L, ?_⟩
  have hP := prodL_nat Φ A B h (fun r : ℕ => s + (r : ℂ)) L
  rw [hL, LinearMap.zero_comp] at hP
  ext v
  apply hΦ
  rw [LinearMap.zero_apply, map_zero]
  simpa using LinearMap.congr_fun hP v

/- English proof (translation)
Take `⟨L, hL⟩` from `h`. Use `⟨L, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun f => funext fun I => ?_` and prove the remaining obligations. Establish `hc : (LinearMap.proj I : TV n V P →ₗ[ℂ] V) ∘ₗ lift X = X ∘ₗ LinearMap.proj I` using `LinearMap.ext fun f => rfl`. Establish `hP` using `prodL_nat (LinearMap.proj I) (lift X) X hc (fun r : ℕ => s + (r : ℂ)) L`.

Rewrite `hP` using `[hL, LinearMap.zero_comp]`. Simplify using `using LinearMap.congr_fun hP f`.
-/
theorem Kl_lift {V P : Type} [AddCommGroup V] [Module ℂ V] (X : Module.End ℂ V) (s : ℂ) (h : Kl X s) :
    Kl (lift X : Module.End ℂ (TV n V P)) s := by
  obtain ⟨L, hL⟩ := h
  refine ⟨L, ?_⟩
  refine LinearMap.ext fun f => funext fun I => ?_
  have hc : (LinearMap.proj I : TV n V P →ₗ[ℂ] V) ∘ₗ lift X = X ∘ₗ LinearMap.proj I :=
    LinearMap.ext fun f => rfl
  have hP := prodL_nat (LinearMap.proj I) (lift X) X hc (fun r : ℕ => s + (r : ℂ)) L
  rw [hL, LinearMap.zero_comp] at hP
  simpa using LinearMap.congr_fun hP f

/- English proof (translation)
Proceed by induction on `Z with`. Consider the case `nil => simp`. Consider the case `cons z Z ih`. Simplify using `only [List.map_cons, List.prod_cons]`. Establish `he : (Y + z) * (Z.map (Y + ·)).prod - z * Z.prod = Y * (Z.map (Y + ·)).prod + z * ((Z.map (Y + ·)).prod - Z.prod)` using `by ring`.

Rewrite using `[he]`. Conclude with `dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right ih _)`.
-/
theorem dvd_prod_shift_sub_prod {R : Type*} [CommRing R] (Y : R) (Z : List R) : Y ∣ (Z.map (Y + ·)).prod - Z.prod := by
  induction Z with
  | nil => simp
  | cons z Z ih =>
    simp only [List.map_cons, List.prod_cons]
    have he : (Y + z) * (Z.map (Y + ·)).prod - z * Z.prod =
        Y * (Z.map (Y + ·)).prod + z * ((Z.map (Y + ·)).prod - Z.prod) := by ring
    rw [he]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right ih _)

/- English proof (translation)
Use `set x : ℕ → R := fun a => A - algebraMap ℂ R (α + a) with hx`. Use `set y : ℕ → R := fun b => B - algebraMap ℂ R (β + b) with hy`. Establish `hA' : (La.map x).prod = 0` using `hA`. Establish `hB' : (Lb.map y).prod = 0` using `hB`. Establish `hterm : ∀ a b : ℕ, A + B - algebraMap ℂ R (α + β + ((a + b : ℕ) : ℂ)) = x a + y b`.

Introduce `a b`. Simplify using `only [hx, hy]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ L : List ℕ, ∃ u v : R, ((L.flatMap fun a => Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod = u * (L.map x).prod + v * (Lb.map y).prod`.

Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => exact ⟨1, 0, by simp⟩`. Consider the case `cons a L ih`. Take `⟨u, v, huv⟩` from `ih`.

Take `⟨c, hc⟩` from `dvd_prod_shift_sub_prod (x a) (Lb.map y)`. Establish `h1 : ((Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod = x a * c + (Lb.map y).prod`. Rewrite using `[← hc, List.map_map, List.map_map]`. Establish `hm : ((fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)) ∘ (a + ·)) = ((x a + ·) ∘ y)`. Use function extensionality and compare the values at `b`.

Conclude with `hterm a b`. Rewrite using `[hm]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨c * u, (x a * c + (Lb.map y).prod) * v + u * (L.map x).prod, ?_⟩` and prove the remaining obligations. Rewrite using `[List.flatMap_cons, List.map_append, List.prod_append, huv, h1]`.

Simplify using `only [List.map_cons, List.prod_cons]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨u, v, huv⟩` from `key La`. Rewrite using `[huv, hA', hB']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_comm {R : Type*} [CommRing R] [Algebra ℂ R] (A B : R) (α β : ℂ) (La Lb : List ℕ)
    (hA : (La.map fun a : ℕ => A - algebraMap ℂ R (α + a)).prod = 0)
    (hB : (Lb.map fun b : ℕ => B - algebraMap ℂ R (β + b)).prod = 0) :
    ((La.flatMap fun a => Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod = 0 := by
  set x : ℕ → R := fun a => A - algebraMap ℂ R (α + a) with hx
  set y : ℕ → R := fun b => B - algebraMap ℂ R (β + b) with hy
  have hA' : (La.map x).prod = 0 := hA
  have hB' : (Lb.map y).prod = 0 := hB
  have hterm : ∀ a b : ℕ, A + B - algebraMap ℂ R (α + β + ((a + b : ℕ) : ℂ)) = x a + y b := by
    intro a b
    simp only [hx, hy]
    push_cast
    ring
  have key : ∀ L : List ℕ, ∃ u v : R,
      ((L.flatMap fun a => Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod =
        u * (L.map x).prod + v * (Lb.map y).prod := by
    intro L
    induction L with
    | nil => exact ⟨1, 0, by simp⟩
    | cons a L ih =>
      obtain ⟨u, v, huv⟩ := ih
      obtain ⟨c, hc⟩ := dvd_prod_shift_sub_prod (x a) (Lb.map y)
      have h1 : ((Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod =
          x a * c + (Lb.map y).prod := by
        rw [← hc, List.map_map, List.map_map]
        have hm : ((fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)) ∘ (a + ·)) =
            ((x a + ·) ∘ y) := by
          funext b
          exact hterm a b
        rw [hm]
        ring
      refine ⟨c * u, (x a * c + (Lb.map y).prod) * v + u * (L.map x).prod, ?_⟩
      rw [List.flatMap_cons, List.map_append, List.prod_append, huv, h1]
      simp only [List.map_cons, List.prod_cons]
      ring
  obtain ⟨u, v, huv⟩ := key La
  rw [huv, hA', hB']
  ring

/- English proof (translation)
Take `⟨La, hLa⟩` from `hA`. Take `⟨Lb, hLb⟩` from `hB`. Use `⟨La.flatMap fun a => Lb.map (a + ·), ?_⟩` and prove the remaining obligations. Establish `hc : ∀ a ∈ ({A, B} : Set (Module.End ℂ V)), ∀ b ∈ ({A, B} : Set (Module.End ℂ V)), a * b = b * a`. Introduce `a ha b hb`.

Apply the tactic sequence `rcases ha with rfl | rfl <;> rcases hb with rfl | rfl`. Both sides reduce to the same expression. Conclude with `hAB.eq`. Conclude with `hAB.eq.symm`. Both sides reduce to the same expression.

Use `letI : CommRing (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))) := Algebra.adjoinCommRingOfComm ℂ hc`. Set `a' : Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))` to `⟨A, Algebra.subset_adjoin (by simp)⟩`. Set `b' : Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))` to `⟨B, Algebra.subset_adjoin (by simp)⟩`. Establish `hinj : Function.Injective (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))).val` using `Subtype.val_injective`. Establish `hA' : (La.map fun a : ℕ => a' - algebraMap ℂ _ (α + a)).prod = 0`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_list_prod, map_zero, List.map_map]`. Simplify `hLa` using `[Function.comp_def, a']`. Establish `hB' : (Lb.map fun b : ℕ => b' - algebraMap ℂ _ (β + b)).prod = 0`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_list_prod, map_zero, List.map_map]`. Simplify `hLb` using `[Function.comp_def, b']`. Establish `hs` using `congrArg (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))).val (sum_comm a' b' α β La Lb hA' hB')`. Rewrite `hs` using `[map_list_prod, map_zero, List.map_map]`. Simplify `hs` using `[Function.comp_def, a', b']`.
-/
theorem Kl_sum {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Module.End ℂ V) (hAB : Commute A B) (α β : ℂ)
    (hA : Kl A α) (hB : Kl B β) : Kl (A + B) (α + β) := by
  obtain ⟨La, hLa⟩ := hA
  obtain ⟨Lb, hLb⟩ := hB
  refine ⟨La.flatMap fun a => Lb.map (a + ·), ?_⟩
  have hc : ∀ a ∈ ({A, B} : Set (Module.End ℂ V)), ∀ b ∈ ({A, B} : Set (Module.End ℂ V)), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hAB.eq
    · exact hAB.eq.symm
    · rfl
  letI : CommRing (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))) := Algebra.adjoinCommRingOfComm ℂ hc
  let a' : Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V)) := ⟨A, Algebra.subset_adjoin (by simp)⟩
  let b' : Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V)) := ⟨B, Algebra.subset_adjoin (by simp)⟩
  have hinj : Function.Injective (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))).val := Subtype.val_injective
  have hA' : (La.map fun a : ℕ => a' - algebraMap ℂ _ (α + a)).prod = 0 := by
    apply hinj
    rw [map_list_prod, map_zero, List.map_map]
    simpa [Function.comp_def, a'] using hLa
  have hB' : (Lb.map fun b : ℕ => b' - algebraMap ℂ _ (β + b)).prod = 0 := by
    apply hinj
    rw [map_list_prod, map_zero, List.map_map]
    simpa [Function.comp_def, b'] using hLb
  have hs := congrArg (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))).val (sum_comm a' b' α β La Lb hA' hB')
  rw [map_list_prod, map_zero, List.map_map] at hs
  simpa [Function.comp_def, a', b'] using hs

/- English proof (translation)
Simplify using `[xJ, Om, lift, eAt, pm, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (I j)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem xJ_apply {m : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m)
    (f : TV n M (Fin m)) (I : Fin m → Fin n) :
    xJ E j f I = ∑ a, E a (I j) (f (Function.update I j a)) +
      ∑ i ∈ Finset.univ.filter (· < j), f (I ∘ Equiv.swap i j) := by
  simp [xJ, Om, lift, eAt, pm, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (I j)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/- English proof (translation)
Establish `h' : ∀ a b v, φ (E₁ a b v) = E₂ a b (φ v)` using `fun a b v => LinearMap.congr_fun (h a b) v`. Use `LinearMap.ext fun f => funext fun I => ?_` and prove the remaining obligations. Simplify using `[xJ_apply, map_add, map_sum, h', LinearMap.compLeft_apply]`.
-/
theorem xJ_nat {m : ℕ} {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    (E₁ : Fin n → Fin n → Module.End ℂ M₁) (E₂ : Fin n → Fin n → Module.End ℂ M₂) (φ : M₁ →ₗ[ℂ] M₂)
    (h : ∀ a b, φ ∘ₗ E₁ a b = E₂ a b ∘ₗ φ) (j : Fin m) :
    LinearMap.compLeft φ (Fin m → Fin n) ∘ₗ xJ E₁ j = xJ E₂ j ∘ₗ LinearMap.compLeft φ (Fin m → Fin n) := by
  have h' : ∀ a b v, φ (E₁ a b v) = E₂ a b (φ v) := fun a b v => LinearMap.congr_fun (h a b) v
  refine LinearMap.ext fun f => funext fun I => ?_
  simp [xJ_apply, map_add, map_sum, h', LinearMap.compLeft_apply]

/- English proof (translation)
Establish `h' : ∀ a b v, φ (G a b v) = H a b (φ v)` using `fun a b v => LinearMap.congr_fun (h a b) v`. Introduce `a b c d`. Use extensionality with `v`. Apply `hφ` to reduce the goal to its premises. Establish `hv` using `LinearMap.congr_fun (hH a b c d) (φ v)`.

Apply the tactic sequence `by_cases hbc : b = c <;> by_cases hda : d = a <;> simpa [h', hbc, hda] using hv`.
-/
theorem glrel_inj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (G : Fin n → Fin n → Module.End ℂ V) (H : Fin n → Fin n → Module.End ℂ W) (φ : V →ₗ[ℂ] W)
    (hφ : Function.Injective φ) (h : ∀ a b, φ ∘ₗ G a b = H a b ∘ₗ φ) (hH : GlRel H) : GlRel G := by
  have h' : ∀ a b v, φ (G a b v) = H a b (φ v) := fun a b v => LinearMap.congr_fun (h a b) v
  intro a b c d
  ext v
  apply hφ
  have hv := LinearMap.congr_fun (hH a b c d) (φ v)
  by_cases hbc : b = c <;> by_cases hda : d = a <;> simpa [h', hbc, hda] using hv

/- English proof (translation)
Introduce `w hw`. Rewrite `hw`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[← Module.End.mul_apply, h.eq, Module.End.mul_apply, hw, map_zero]`.
-/
theorem ker_stable {V : Type} [AddCommGroup V] [Module ℂ V] (Y X : Module.End ℂ V) (h : Commute Y X) :
    ∀ w ∈ LinearMap.ker Y, X w ∈ LinearMap.ker Y := by
  intro w hw
  rw [LinearMap.mem_ker] at hw ⊢
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply, hw, map_zero]

/- English proof (translation)
Use `Commute.list_prod_left _ _ fun x hx => ?_` and prove the remaining obligations. Take `⟨c, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `h.sub_left (Algebra.commute_algebraMap_left _ _)`.
-/
theorem comm_prod {V : Type} [AddCommGroup V] [Module ℂ V] (A X : Module.End ℂ V) (h : Commute A X)
    {ι : Type} (g : ι → ℂ) (L : List ι) : Commute (L.map fun c => A - algebraMap ℂ _ (g c)).prod X := by
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  exact h.sub_left (Algebra.commute_algebraMap_left _ _)

/- English proof (translation)
Proceed by induction on `ks with`. Consider the case `nil`. Use `⟨[], fun f hf => ?_⟩` and prove the remaining obligations. Establish `hf0 : f = 0` using `funext fun I => by simpa using hf I`. Simplify using `[hf0]`.

Consider the case `cons c ks ih`. Take `⟨L2, hL2⟩` from `ih`. Use `set Y : Module.End ℂ V := (ks.map fun c => A - algebraMap ℂ _ (l c)).prod with hYdef`. Use `set Z : Module.End ℂ V := A - algebraMap ℂ _ (l c) with hZ`. Establish `hZG : ∀ a b, Commute Z (G a b)` using `fun a b => (hGA a b).sub_left (Algebra.commute_algebraMap_left _ _)`.

Establish `hZA : Commute Z A` using `(Commute.refl A).sub_left (Algebra.commute_algebraMap_left _ _)`. Establish `hW : ∀ a b, ∀ w ∈ LinearMap.ker Z, G a b w ∈ LinearMap.ker Z` using `fun a b => ker_stable Z (G a b) (hZG a b)`. Establish `hWA : ∀ w ∈ LinearMap.ker Z, A w ∈ LinearMap.ker Z` using `ker_stable Z A hZA`. Set `F : Fin n → Fin n → Module.End ℂ (LinearMap.ker Z)` to `fun a b => LinearMap.codRestrict (LinearMap.ker Z) ((G a b).comp (LinearMap.ker Z).subtype) (fun w => hW a b w w.2)`. Establish `hsub : ∀ a b, (LinearMap.ker Z).subtype ∘ₗ F a b = G a b ∘ₗ (LinearMap.ker Z).subtype` using `fun a b => LinearMap.ext fun w => rfl`.

Establish `hF : GlRel F` using `glrel_inj F G (LinearMap.ker Z).subtype (LinearMap.ker Z).injective_subtype hsub hG`. Establish `hKl` using `H (LinearMap.ker Z) hW hWA c (LinearMap.ker Z) F LinearMap.id hF Function.surjective_id (fun a b w => rfl) (fun w => by`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hw : (A - algebraMap ℂ (Module.End ℂ V) (l c)) (w : V) = 0` using `LinearMap.mem_ker.1 w.2`. Rewrite `hw` using `[LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]`.

Simplify using `using hw)`. Take `⟨L1, hL1⟩` from `hKl`. Establish `hΦ` using `prodL_nat (LinearMap.compLeft (LinearMap.ker Z).subtype (Fin k → Fin n)) (xJ F j) (xJ G j) (xJ_nat F G (LinearMap.ker Z).subtype hsub j) (fun r : ℕ => s + (r : ℂ)) L1`. Rewrite `hΦ` using `[hL1, LinearMap.comp_zero]`. Establish `hYG : ∀ a b, Y ∘ₗ G a b = G a b ∘ₗ Y` using `fun a b => by`.

Rewrite using `[← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]`. Conclude with `(comm_prod A (G a b) (hGA a b) l ks).eq`. Establish `hΨ` using `prodL_nat (LinearMap.compLeft Y (Fin k → Fin n)) (xJ G j) (xJ G j) (xJ_nat G G Y hYG j) (fun r : ℕ => s + (r : ℂ)) L1`. Use `⟨L2 ++ L1, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_append, List.prod_append, Module.End.mul_apply]`.

Apply `hL2` to reduce the goal to its premises. Introduce `I`. Establish `hf' : ∀ I, Y (f I) ∈ LinearMap.ker Z` using `fun I => by`. Establish `hI` using `hf I`. Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply] at hI`.

Conclude with `LinearMap.mem_ker.2 hI`. Establish `h0` using `LinearMap.congr_fun hΦ (fun I => (⟨Y (f I), hf' I⟩ : LinearMap.ker Z))`. Establish `h1` using `LinearMap.congr_fun hΨ f`. Rewrite `h0`, `h1` using `[LinearMap.comp_apply]`. Rewrite `h1` using `[LinearMap.comp_apply]`.

Establish `h2 : (LinearMap.compLeft (LinearMap.ker Z).subtype (Fin k → Fin n)) (fun I => (⟨Y (f I), hf' I⟩ : LinearMap.ker Z)) = (LinearMap.compLeft Y (Fin k → Fin n)) f` using `rfl`. Rewrite `h0` using `[h2, ← h1]`. Establish `h3` using `congrFun h0.symm I`. Simplify using `using h3`.
-/
theorem filt {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (G : Fin n → Fin n → Module.End ℂ V)
    (A : Module.End ℂ V) (hG : GlRel G) (hGA : ∀ a b, Commute A (G a b)) (l : Fin n → ℂ) (s : ℂ) (j : Fin k)
    (H : ∀ (W : Submodule ℂ V) (hW : ∀ a b, ∀ w ∈ W, G a b w ∈ W) (hA : ∀ w ∈ W, A w ∈ W) (c : Fin n)
      (N : Type) [AddCommGroup N] [Module ℂ N] (F : Fin n → Fin n → Module.End ℂ N) (q : W →ₗ[ℂ] N),
      GlRel F → Function.Surjective q → (∀ a b (w : W), q ⟨_, hW a b w w.2⟩ = F a b (q w)) →
      (∀ w : W, q ⟨_, hA w w.2⟩ = l c • q w) → Kl (xJ F j) s)
    (ks : List (Fin n)) : ∃ L : List ℕ, ∀ f : TV n V (Fin k),
      (∀ I, (ks.map fun c => A - algebraMap ℂ _ (l c)).prod (f I) = 0) →
      (L.map fun r : ℕ => xJ G j - algebraMap ℂ _ (s + r)).prod f = 0 := by
  induction ks with
  | nil =>
    refine ⟨[], fun f hf => ?_⟩
    have hf0 : f = 0 := funext fun I => by simpa using hf I
    simp [hf0]
  | cons c ks ih =>
    obtain ⟨L2, hL2⟩ := ih
    set Y : Module.End ℂ V := (ks.map fun c => A - algebraMap ℂ _ (l c)).prod with hYdef
    set Z : Module.End ℂ V := A - algebraMap ℂ _ (l c) with hZ
    have hZG : ∀ a b, Commute Z (G a b) := fun a b =>
      (hGA a b).sub_left (Algebra.commute_algebraMap_left _ _)
    have hZA : Commute Z A := (Commute.refl A).sub_left (Algebra.commute_algebraMap_left _ _)
    have hW : ∀ a b, ∀ w ∈ LinearMap.ker Z, G a b w ∈ LinearMap.ker Z :=
      fun a b => ker_stable Z (G a b) (hZG a b)
    have hWA : ∀ w ∈ LinearMap.ker Z, A w ∈ LinearMap.ker Z := ker_stable Z A hZA
    let F : Fin n → Fin n → Module.End ℂ (LinearMap.ker Z) := fun a b =>
      LinearMap.codRestrict (LinearMap.ker Z) ((G a b).comp (LinearMap.ker Z).subtype) (fun w => hW a b w w.2)
    have hsub : ∀ a b, (LinearMap.ker Z).subtype ∘ₗ F a b = G a b ∘ₗ (LinearMap.ker Z).subtype :=
      fun a b => LinearMap.ext fun w => rfl
    have hF : GlRel F := glrel_inj F G (LinearMap.ker Z).subtype (LinearMap.ker Z).injective_subtype hsub hG
    have hKl := H (LinearMap.ker Z) hW hWA c (LinearMap.ker Z) F LinearMap.id hF Function.surjective_id
      (fun a b w => rfl) (fun w => by
        apply Subtype.ext
        have hw : (A - algebraMap ℂ (Module.End ℂ V) (l c)) (w : V) = 0 := LinearMap.mem_ker.1 w.2
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at hw
        simpa using hw)
    obtain ⟨L1, hL1⟩ := hKl
    have hΦ := prodL_nat (LinearMap.compLeft (LinearMap.ker Z).subtype (Fin k → Fin n)) (xJ F j) (xJ G j)
      (xJ_nat F G (LinearMap.ker Z).subtype hsub j) (fun r : ℕ => s + (r : ℂ)) L1
    rw [hL1, LinearMap.comp_zero] at hΦ
    have hYG : ∀ a b, Y ∘ₗ G a b = G a b ∘ₗ Y := fun a b => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
      exact (comm_prod A (G a b) (hGA a b) l ks).eq
    have hΨ := prodL_nat (LinearMap.compLeft Y (Fin k → Fin n)) (xJ G j) (xJ G j) (xJ_nat G G Y hYG j)
      (fun r : ℕ => s + (r : ℂ)) L1
    refine ⟨L2 ++ L1, fun f hf => ?_⟩
    rw [List.map_append, List.prod_append, Module.End.mul_apply]
    apply hL2
    intro I
    have hf' : ∀ I, Y (f I) ∈ LinearMap.ker Z := fun I => by
      have hI := hf I
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply] at hI
      exact LinearMap.mem_ker.2 hI
    have h0 := LinearMap.congr_fun hΦ (fun I => (⟨Y (f I), hf' I⟩ : LinearMap.ker Z))
    have h1 := LinearMap.congr_fun hΨ f
    rw [LinearMap.comp_apply] at h0 h1
    rw [LinearMap.comp_apply] at h1
    have h2 : (LinearMap.compLeft (LinearMap.ker Z).subtype (Fin k → Fin n))
        (fun I => (⟨Y (f I), hf' I⟩ : LinearMap.ker Z)) = (LinearMap.compLeft Y (Fin k → Fin n)) f := rfl
    rw [h2, ← h1] at h0
    have h3 := congrFun h0.symm I
    simpa using h3

def Cl (k : ℕ) : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ (l : Fin n → ℂ) (s : ℂ), HasChar E l → (∀ k, ∃ r : ℕ, l k = s + r) → ∀ j : Fin k, Kl (xJ E j) s

/- English proof (translation)
Introduce `n M _ _ E hE l s hl hls j`. Take `⟨hbij, -, hcast, hnat, -, -, -⟩` from `h3 n M E 1 k`. Take `⟨hstep1, hstep2⟩` from `h5 n M E hE l hl`. Use `choose r hr using hls`. Proceed by induction on `j using Fin.addCases with`.

Consider the case `left i`. Establish `hi : i = 0` using `Subsingleton.elim i 0`. Substitute `hi` using the available equality. Apply `Kl_nat (curF n M 1 k) hbij.1 _ _ (hcast 0)` to reduce the goal to its premises. Apply `Kl_lift` to reduce the goal to its premises.

Use `⟨List.ofFn r, ?_⟩` and prove the remaining obligations. Establish `hx : xJ E (0 : Fin 1) = Om E 0` using `by simp [xJ]`. Establish `he : (List.ofFn r).map (fun r : ℕ => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (s + r)) = List.ofFn fun c => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (l c)`. Rewrite using `[List.map_ofFn]`. Use `congr 1`.

Use function extensionality and compare the values at `c`. Simplify using `[hr c]`. Rewrite using `[hx, he]`. Conclude with `hstep1`. Consider the case `right j'`.

Apply `Kl_nat (curF n M 1 k) hbij.1 _ _ (hnat j')` to reduce the goal to its premises. Take `⟨hG, hGA, -, -⟩` from `h1 n M (Fin 1) E hE Finset.univ`. Establish `hls' : ∀ c c', ∃ r' : ℕ, Function.update l c (l c + 1) c' = s + r'`. Introduce `c c'`. Distinguish the cases in `hcc : c' = c`.

Substitute `hcc` using the available equality. Use `⟨r c' + 1, ?_⟩` and prove the remaining obligations. Simplify using `[hr c']`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨r c', by simp [hcc, hr c']⟩`.

Take `⟨L, hL⟩` from `filt (tE Finset.univ E) (Om E 0) hG (fun a b => hGA 0 (Finset.mem_univ _) a b) l s j' (by`. Introduce `W hW hA c N _ _ F q hF hq hFq hAq`. Conclude with `ih n N F hF (Function.update l c (l c + 1)) s (hstep2 W N F q hW hA c hq hFq hAq) (hls' c) j')`. Use the proof step `(List.finRange n)`. Establish `h0 : ((List.finRange n).map fun c => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (l c)).prod = 0`.

Rewrite using `[← List.ofFn_eq_map]`. Conclude with `hstep1`. Use `⟨L, LinearMap.ext fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.zero_apply]`. Conclude with `hL f (fun I => by rw [h0]; rfl)`.
-/
theorem cl_step (h1 : TensorGl) (h3 : Curry) (h5 : StepChar) (k : ℕ) (ih : Cl k) : Cl (1 + k) := by
  intro n M _ _ E hE l s hl hls j
  obtain ⟨hbij, -, hcast, hnat, -, -, -⟩ := h3 n M E 1 k
  obtain ⟨hstep1, hstep2⟩ := h5 n M E hE l hl
  choose r hr using hls
  induction j using Fin.addCases with
  | left i =>
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    apply Kl_nat (curF n M 1 k) hbij.1 _ _ (hcast 0)
    apply Kl_lift
    refine ⟨List.ofFn r, ?_⟩
    have hx : xJ E (0 : Fin 1) = Om E 0 := by simp [xJ]
    have he : (List.ofFn r).map (fun r : ℕ => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (s + r)) =
        List.ofFn fun c => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (l c) := by
      rw [List.map_ofFn]
      congr 1
      funext c
      simp [hr c]
    rw [hx, he]
    exact hstep1
  | right j' =>
    apply Kl_nat (curF n M 1 k) hbij.1 _ _ (hnat j')
    obtain ⟨hG, hGA, -, -⟩ := h1 n M (Fin 1) E hE Finset.univ
    have hls' : ∀ c c', ∃ r' : ℕ, Function.update l c (l c + 1) c' = s + r' := by
      intro c c'
      by_cases hcc : c' = c
      · subst hcc
        refine ⟨r c' + 1, ?_⟩
        simp [hr c']
        ring
      · exact ⟨r c', by simp [hcc, hr c']⟩
    obtain ⟨L, hL⟩ := filt (tE Finset.univ E) (Om E 0) hG (fun a b => hGA 0 (Finset.mem_univ _) a b) l s j'
      (by
        intro W hW hA c N _ _ F q hF hq hFq hAq
        exact ih n N F hF (Function.update l c (l c + 1)) s (hstep2 W N F q hW hA c hq hFq hAq) (hls' c) j')
      (List.finRange n)
    have h0 : ((List.finRange n).map fun c => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (l c)).prod = 0 := by
      rw [← List.ofFn_eq_map]
      exact hstep1
    refine ⟨L, LinearMap.ext fun f => ?_⟩
    rw [LinearMap.zero_apply]
    exact hL f (fun I => by rw [h0]; rfl)

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `n M _ _ E hE l s hl hls j`. Conclude with `j.elim0`.

Consider the case `succ m ih`. Rewrite using `[Nat.add_comm]`. Conclude with `cl_step h1 h3 h5 m ih`.
-/
theorem cl_all (h1 : TensorGl) (h3 : Curry) (h5 : StepChar) : ∀ m, Cl m := by
  intro m
  induction m with
  | zero =>
    intro n M _ _ E hE l s hl hls j
    exact j.elim0
  | succ m ih =>
    rw [Nat.add_comm]
    exact cl_step h1 h3 h5 m ih

end SpecA

/- English proof (translation)
Introduce `h1 h2 h3 h5 n M _ _ E hE l s hl hls m`. Establish `hcl : ∀ j : Fin m, SpecA.Kl (xJ E j) s` using `SpecA.cl_all h1 h3 h5 m n M E hE l s hl hls`. Establish `hcomm` using `(h2 n M E hE m).1`. Establish `hsum : ∀ k, k ≤ m → SpecA.Kl (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), xJ E j) ((k : ℂ) * s)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`. Use `⟨[0], ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Consider the case `succ k ihk`. Introduce `hk`. Establish `hk' : k < m` using `hk`. Establish `hfil : (Finset.univ.filter fun j : Fin m => (j : ℕ) < k + 1) = insert ⟨k, hk'⟩ (Finset.univ.filter fun j : Fin m => (j : ℕ) < k)`. Use extensionality with `j`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hsplit : (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k + 1), xJ E j) = (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), xJ E j) + xJ E ⟨k, hk'⟩`. Rewrite using `[hfil, Finset.sum_insert (by simp), add_comm]`. Rewrite using `[hsplit, show ((k + 1 : ℕ) : ℂ) * s = (k : ℂ) * s + s by push_cast; ring]`.

Conclude with `SpecA.Kl_sum _ _ (Commute.sum_left _ _ _ fun j _ => hcomm j ⟨k, hk'⟩) _ _ (ihk (by omega)) (hcl ⟨k, hk'⟩)`. Conclude with `⟨fun k hk => hsum k hk, hcl⟩`.
-/
theorem spectrum_of : TensorGl → JMComm → Curry → StepChar → Spectrum := by
  intro h1 h2 h3 h5 n M _ _ E hE l s hl hls m
  have hcl : ∀ j : Fin m, SpecA.Kl (xJ E j) s := SpecA.cl_all h1 h3 h5 m n M E hE l s hl hls
  have hcomm := (h2 n M E hE m).1
  have hsum : ∀ k, k ≤ m →
      SpecA.Kl (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), xJ E j) ((k : ℂ) * s) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[0], ?_⟩
      simp
    | succ k ihk =>
      intro hk
      have hk' : k < m := hk
      have hfil : (Finset.univ.filter fun j : Fin m => (j : ℕ) < k + 1) =
          insert ⟨k, hk'⟩ (Finset.univ.filter fun j : Fin m => (j : ℕ) < k) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hsplit : (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k + 1), xJ E j) =
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), xJ E j) + xJ E ⟨k, hk'⟩ := by
        rw [hfil, Finset.sum_insert (by simp), add_comm]
      rw [hsplit, show ((k + 1 : ℕ) : ℂ) * s = (k : ℂ) * s + s by push_cast; ring]
      exact SpecA.Kl_sum _ _ (Commute.sum_left _ _ _ fun j _ => hcomm j ⟨k, hk'⟩) _ _ (ihk (by omega)) (hcl ⟨k, hk'⟩)
  exact ⟨fun k hk => hsum k hk, hcl⟩

end PositivityTheory.Rg.Cz

end
