import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Introduce `i hi`. Use `⟨?_, fun j hj => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f (k.val i i) = 1`. Rewrite using `[(h i hi).1, map_one]`. Express the relevant statement in the definitionally equal form `f (k.val i j) = 0`.

Rewrite using `[(h i hi).2 j hj, map_zero]`.
-/
private theorem isY_map {R S : Type} [CommRing R] [CommRing S] {n m : ℕ} (f : R →+* S) {k : GL (Fin n) R}
    (h : IsY m k.val) : IsY m (GeneralLinearGroup.map f k).val := by
  intro i hi
  refine ⟨?_, fun j hj => ?_⟩
  · change f (k.val i i) = 1
    rw [(h i hi).1, map_one]
  · change f (k.val i j) = 0
    rw [(h i hi).2 j hj, map_zero]

/- English proof (translation)
Introduce `i _`. Conclude with `⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩`.
-/
private theorem isY_one {R : Type} [CommRing R] {n m : ℕ} : IsY m (1 : GL (Fin n) R).val := by
  intro i _
  exact ⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩

/- English proof (translation)
Introduce `i hi`. Use `⟨DFunLike.ext _ _ fun w => ?_, fun j hj => DFunLike.ext _ _ fun w => ?_⟩` and prove the remaining obligations. Conclude with `(h w i hi).1`. Conclude with `(h w i hi).2 j hj`.
-/
private theorem isY_of_cmp {E : Type} [Field E] [NumberField E] {n m : ℕ} {k : GL (Fin n) (Af E)}
    (h : ∀ w, IsY m (cmp w k).val) : IsY m k.val := by
  intro i hi
  refine ⟨DFunLike.ext _ _ fun w => ?_, fun j hj => DFunLike.ext _ _ fun w => ?_⟩
  · exact (h w i hi).1
  · exact (h w i hi).2 j hj

/- English proof (translation)
Use `cmp_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Rewrite using `[hk, one_mul, mul_one]`.

Rewrite using `[show cmp v (locGL E n w y) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv y, one_mul, mul_one]`.
-/
private theorem loc_comm {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)}
    {k : GL (Fin n) (Af E)} (hk : cmp w k = 1) (y : GL (Fin n) (w.adicCompletion E)) :
    k * locGL E n w y = locGL E n w y * k := by
  refine cmp_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases hv : v = w
  · subst hv
    rw [hk, one_mul, mul_one]
  · rw [show cmp v (locGL E n w y) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv y, one_mul, mul_one]

/- English proof (translation)
Introduce `w hw` and use `by rw [map_mul, ha w hw, hb w hw, mul_one]`.
-/
private theorem supp_mul {E : Type} [Field E] [NumberField E] {n : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {a b : GL (Fin n) (Af E)} (ha : SuppIn S a) (hb : SuppIn S b) : SuppIn S (a * b) := fun w hw => by
  rw [map_mul, ha w hw, hb w hw, mul_one]

/- English proof (translation)
Introduce `v hv` and use `GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : v = w => hv (e ▸ hw)) y`.
-/
private theorem supp_loc {E : Type} [Field E] [NumberField E] {n : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) (y : GL (Fin n) (w.adicCompletion E)) :
    SuppIn S (locGL E n w y) := fun v hv =>
  GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : v = w => hv (e ▸ hw)) y

/- English proof (translation)
Unfold `comb`. Rewrite using `[Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]`. Simplify using `only [map_mul, mul_assoc]`.
-/
private theorem comb_mapDomain {G G' : Type} [Group G] [Group G'] (f : G →* G') (c : G →₀ ℂ) (W : G' → ℂ)
    (g : G') (p : G) : comb (c.mapDomain f) W (g * f p) = comb c (fun y => W (g * f y)) p := by
  unfold comb
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]
  simp only [map_mul, mul_assoc]

/- English proof (translation)
Introduce `hK hP hE E _ _ _ n hn S U`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Use `⟨Finsupp.single 1 1, fun _ => 1, rfl, fun x hx => ?_, fun W _ _ p hp _ => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]`.

Conclude with `fun w _ => map_one _`. Take `rfl : p = 1` from `cmp_ext fun w => (hp w (Finset.notMem_empty w)).trans (map_one _).symm`. Unfold `comb`. Rewrite using `[Finsupp.sum_single_index (by simp), mul_one]`. Consider the case `insert w S hw ih`.

Take `⟨c₁, H₁, h1, hs₁, hc₁⟩` from `ih`. Take `⟨hE1, -, -, hEc⟩` from `hE E n 0`. Take `⟨c₀, H₀, h0, hc₀⟩` from `hK E w (psiL w) ((hP E).1 w).1 ((hP E).1 w).2 n (n - 1) (by omega) (U.comap (locGL E n w) (hEc w))`. Take `⟨c, hs, hc⟩` from `exists_comb_comb c₁ (c₀.mapDomain (locGL E n w))`. Establish `mono : ∀ {k : GL (Fin n) (Af E)}, SuppIn S k → SuppIn (insert w S) k` using `fun hk v hv => hk v fun h => hv (Finset.mem_insert_of_mem h)`.

Establish `hl : ∀ y, SuppIn (insert w S) (locGL E n w y)` using `supp_loc (Finset.mem_insert_self w S)`. Use `⟨c, fun p => H₀ (cmp w p) * H₁ (p * (locGL E n w (cmp w p))⁻¹), ?_, fun x hx => ?_, fun W hW hU p hp hY => ?_⟩` and prove the remaining obligations. Simplify using `only [map_one, inv_one, mul_one, h0, h1]`. Take `⟨a, ha, b, hb, rfl⟩` from `hs x hx`. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hb)`.

Conclude with `supp_mul (mono (hs₁ a ha)) (hl y)`. Establish `key : ∀ g, SuppIn S g → comb (c₀.mapDomain (locGL E n w)) W (g * locGL E n w (cmp w p)) = H₀ (cmp w p) * W g`. Introduce `g hg`. Rewrite using `[comb_mapDomain, hc₀ (fun y => W (g * locGL E n w y)) ?_ ?_ _ (isY_map _ hY), map_one, mul_one]`. Introduce `ν hν y beta_reduce`.

Rewrite using `[map_mul, ← mul_assoc, loc_comm (hg w hw), mul_assoc, hW _ (hl ν) (hE1 w ν hν).1 _ (supp_mul (mono hg) (hl y)), (hE1 w ν hν).2]`. Both sides reduce to the same expression. Introduce `y u hu beta_reduce`. Rewrite using `[map_mul, ← mul_assoc]`. Conclude with `hU _ (supp_mul (mono hg) (hl y)) _ hu (hl u)`.

Use `set p' := p * (locGL E n w (cmp w p))⁻¹ with hp'`. Establish `e0 : cmp w p' = 1`. Rewrite using `[hp', map_mul, map_inv, show cmp w (locGL E n w (cmp w p)) = cmp w p from GlobalTheory.CuspRep.pLoc_locGL w _, mul_inv_cancel]`. Establish `e1 : ∀ v, v ≠ w → cmp v p' = cmp v p` using `fun v hv => by`. Rewrite using `[hp', map_mul, map_inv, show cmp v (locGL E n w (cmp w p)) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv _, inv_one, mul_one]`.

Establish `hS : SuppIn S p'` using `fun v hv => by`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Conclude with `e0`. Rewrite using `[e1 v h]`.

Conclude with `hp v fun h' => (Finset.mem_insert.1 h').elim h hv`. Establish `hY' : IsY (n - 1) p'.val` using `isY_of_cmp fun v => by`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Rewrite using `[e0]`.

Conclude with `isY_one`. Rewrite using `[e1 v h]`. Conclude with `isY_map _ hY`. Establish `ep : p = p' * locGL E n w (cmp w p)` using `by rw [hp', inv_mul_cancel_right]`. Establish `hI` using `hc₁ W (fun ν hν hy g hg => hW ν (mono hν) hy g (mono hg)) (fun g hg u hu hu' => hU g (mono hg) u hu (mono hu')) p' hS hY'`.

Rewrite using `[hc, mul_assoc, ← hI]`. Unfold `comb at key ⊢`. Rewrite using `[Finsupp.mul_sum]`. Use `Finsupp.sum_congr fun x hx => ?_` and prove the remaining obligations. Establish `e2 : p * x = p' * x * locGL E n w (cmp w p)`.

Rewrite using `[mul_assoc, loc_comm (hs₁ x hx w hw), ← mul_assoc, ← ep]`. Rewrite using `[e2, key _ (supp_mul hS (hs₁ x hx))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Af.Smo.finKir :
    UpperTheory.V.Af.Smo.LocKir → UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.Smo.EmbY → UpperTheory.V.Af.Smo.FinKir := by
  classical
  intro hK hP hE E _ _ _ n hn S U
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨Finsupp.single 1 1, fun _ => 1, rfl, fun x hx => ?_, fun W _ _ p hp _ => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact fun w _ => map_one _
    · obtain rfl : p = 1 := cmp_ext fun w => (hp w (Finset.notMem_empty w)).trans (map_one _).symm
      unfold comb
      rw [Finsupp.sum_single_index (by simp), mul_one]
  | insert w S hw ih =>
    obtain ⟨c₁, H₁, h1, hs₁, hc₁⟩ := ih
    obtain ⟨hE1, -, -, hEc⟩ := hE E n 0
    obtain ⟨c₀, H₀, h0, hc₀⟩ := hK E w (psiL w) ((hP E).1 w).1 ((hP E).1 w).2 n (n - 1) (by omega)
      (U.comap (locGL E n w) (hEc w))
    obtain ⟨c, hs, hc⟩ := exists_comb_comb c₁ (c₀.mapDomain (locGL E n w))
    have mono : ∀ {k : GL (Fin n) (Af E)}, SuppIn S k → SuppIn (insert w S) k :=
      fun hk v hv => hk v fun h => hv (Finset.mem_insert_of_mem h)
    have hl : ∀ y, SuppIn (insert w S) (locGL E n w y) := supp_loc (Finset.mem_insert_self w S)
    refine ⟨c, fun p => H₀ (cmp w p) * H₁ (p * (locGL E n w (cmp w p))⁻¹), ?_, fun x hx => ?_,
      fun W hW hU p hp hY => ?_⟩
    · simp only [map_one, inv_one, mul_one, h0, h1]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hs x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hb)
      exact supp_mul (mono (hs₁ a ha)) (hl y)
    · have key : ∀ g, SuppIn S g → comb (c₀.mapDomain (locGL E n w)) W (g * locGL E n w (cmp w p))
          = H₀ (cmp w p) * W g := by
        intro g hg
        rw [comb_mapDomain, hc₀ (fun y => W (g * locGL E n w y)) ?_ ?_ _ (isY_map _ hY), map_one, mul_one]
        · intro ν hν y
          beta_reduce
          rw [map_mul, ← mul_assoc, loc_comm (hg w hw), mul_assoc,
            hW _ (hl ν) (hE1 w ν hν).1 _ (supp_mul (mono hg) (hl y)), (hE1 w ν hν).2]
          rfl
        · intro y u hu
          beta_reduce
          rw [map_mul, ← mul_assoc]
          exact hU _ (supp_mul (mono hg) (hl y)) _ hu (hl u)
      set p' := p * (locGL E n w (cmp w p))⁻¹ with hp'
      have e0 : cmp w p' = 1 := by
        rw [hp', map_mul, map_inv, show cmp w (locGL E n w (cmp w p)) = cmp w p from GlobalTheory.CuspRep.pLoc_locGL w _,
          mul_inv_cancel]
      have e1 : ∀ v, v ≠ w → cmp v p' = cmp v p := fun v hv => by
        rw [hp', map_mul, map_inv, show cmp v (locGL E n w (cmp w p)) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv _,
          inv_one, mul_one]
      have hS : SuppIn S p' := fun v hv => by
        by_cases h : v = w
        · subst h; exact e0
        · rw [e1 v h]
          exact hp v fun h' => (Finset.mem_insert.1 h').elim h hv
      have hY' : IsY (n - 1) p'.val := isY_of_cmp fun v => by
        by_cases h : v = w
        · subst h; rw [e0]; exact isY_one
        · rw [e1 v h]; exact isY_map _ hY
      have ep : p = p' * locGL E n w (cmp w p) := by rw [hp', inv_mul_cancel_right]
      have hI := hc₁ W (fun ν hν hy g hg => hW ν (mono hν) hy g (mono hg))
        (fun g hg u hu hu' => hU g (mono hg) u hu (mono hu')) p' hS hY'
      rw [hc, mul_assoc, ← hI]
      unfold comb at key ⊢
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun x hx => ?_
      have e2 : p * x = p' * x * locGL E n w (cmp w p) := by
        rw [mul_assoc, loc_comm (hs₁ x hx w hw), ← mul_assoc, ← ep]
      rw [e2, key _ (supp_mul hS (hs₁ x hx))]
      ring
