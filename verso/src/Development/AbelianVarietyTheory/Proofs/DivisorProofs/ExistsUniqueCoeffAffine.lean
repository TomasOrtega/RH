import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)
open GlobalTheory.InvFieldBasis hiding existsUnique_coeff_alg existsUnique_coeff_affine existsUnique_coeff

noncomputable section

namespace GlobalTheory.KSUniq

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C]

/- English proof (translation)
Establish `e : x₀ = spMap (evalPt x₀ U hx) ≫ hU.fromSpec` using `eq_spec_fromSpec hU x₀ hx`. Use `⟨pullback p hU.fromSpec, pullback.snd _ _, pullback.fst _ _, inferInstance, pullback.lift m (h₀ ≫ spMap (evalPt x₀ U hx)) (by rw [H.w, Category.assoc]; exact congrArg (h₀ ≫ ·) e), evalPt x₀ U hx, pullback.lift_fst _ _ _, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[pullback.lift_fst, ← e]`. Conclude with `H`.

Rewrite using `[Scheme.Hom.opensRange_pullbackFst, hU.opensRange_fromSpec]`. Introduce `W hW r`. Establish `key : p.appLE U W hW ≫ (pullback.fst p hU.fromSpec).app W = (Scheme.ΓSpecIso (CommRingCat.of Γ(S, U))).inv ≫ (pullback.snd p hU.fromSpec).appLE ⊤ (pullback.fst p hU.fromSpec ⁻¹ᵁ W) (fun _ _ => trivial)`. Rewrite using `[Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]`. Simplify using `only [pullback.condition]`.

Rewrite using `[Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_self, Category.assoc]`. Use `congr 1`. Conclude with `Scheme.Hom.map_appLE _ _ _`. Rewrite using `[pbT, dif_pos hW, constFn]`. Conclude with `congrArg (fun φ => φ.hom r) key`.
-/
private theorem exists_openImmersion_restrict_pullback_constFn {S X A : Scheme.{0}} (x₀ : Sp K ⟶ S) (p : X ⟶ S) (h₀ : A ⟶ Sp K)
    (m : A ⟶ X) (H : IsPullback m h₀ p x₀) {U : S.Opens} (hU : IsAffineOpen U)
    (hx : ⊤ ≤ x₀ ⁻¹ᵁ U) :
    ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp Γ(S, U)) (q : X' ⟶ X) (hq : IsOpenImmersion q) (m' : A ⟶ X')
      (x₀' : Γ(S, U) →+* K), m' ≫ q = m ∧ IsPullback m' h₀ p' (spMap x₀') ∧
      @Scheme.Hom.opensRange _ _ q hq = p ⁻¹ᵁ U ∧
      ∀ (W : X.Opens), W ≤ p ⁻¹ᵁ U → ∀ r : Γ(S, U),
        (q.app W).hom (pbT p r W) = constFn p' (q ⁻¹ᵁ W) r := by

  have e : x₀ = spMap (evalPt x₀ U hx) ≫ hU.fromSpec := eq_spec_fromSpec hU x₀ hx
  refine ⟨pullback p hU.fromSpec, pullback.snd _ _, pullback.fst _ _, inferInstance,
    pullback.lift m (h₀ ≫ spMap (evalPt x₀ U hx))
      (by rw [H.w, Category.assoc]; exact congrArg (h₀ ≫ ·) e),
    evalPt x₀ U hx, pullback.lift_fst _ _ _, ?_, ?_, ?_⟩
  · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, ← e]
    exact H
  · rw [Scheme.Hom.opensRange_pullbackFst, hU.opensRange_fromSpec]
  · intro W hW r
    have key : p.appLE U W hW ≫ (pullback.fst p hU.fromSpec).app W =
        (Scheme.ΓSpecIso (CommRingCat.of Γ(S, U))).inv ≫
          (pullback.snd p hU.fromSpec).appLE ⊤ (pullback.fst p hU.fromSpec ⁻¹ᵁ W)
            (fun _ _ => trivial) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      simp only [pullback.condition]
      rw [Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_self, Category.assoc]
      congr 1
      exact Scheme.Hom.map_appLE _ _ _
    rw [pbT, dif_pos hW, constFn]
    exact congrArg (fun φ => φ.hom r) key

/- English proof (translation)
Apply `hx` to reduce the goal to its premises. Introduce `z _`. Establish `h1 : p (m (y t)) ∈ U` using `@hW (m (y t)) ht`. Establish `h2 : (m ≫ p) (y t) = (h₀ ≫ x₀) (y t)` using `by rw [H.w]`. Rewrite `h2` using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`.

Establish `h3 : z = h₀ (y t)` using `Subsingleton.elim (α := PrimeSpectrum K) _ _`. Rewrite using `[Scheme.Hom.mem_preimage, h3, ← h2]`. Conclude with `h1`.
-/
private theorem false_of_pullback_point_mem_preimage_of_not_univ_le {S X A T : Scheme.{0}} (x₀ : Sp K ⟶ S) (p : X ⟶ S) (h₀ : A ⟶ Sp K)
    (m : A ⟶ X) (H : IsPullback m h₀ p x₀) {U : S.Opens} (hx : ¬ ⊤ ≤ x₀ ⁻¹ᵁ U) (y : T ⟶ A)
    {W : X.Opens} (hW : W ≤ p ⁻¹ᵁ U) (t : T) (ht : t ∈ y ⁻¹ᵁ (m ⁻¹ᵁ W)) : False := by

  apply hx
  intro z _
  have h1 : p (m (y t)) ∈ U := @hW (m (y t)) ht
  have h2 : (m ≫ p) (y t) = (h₀ ≫ x₀) (y t) := by rw [H.w]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h2
  have h3 : z = h₀ (y t) := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [Scheme.Hom.mem_preimage, h3, ← h2]
  exact h1

/- English proof (translation)
Distinguish the cases in `hx : ⊤ ≤ x₀ ⁻¹ᵁ U`. Take `⟨X', p', q, hq, m', x₀', rfl, H', hr, hb⟩` from `exists_openImmersion_restrict_pullback_constFn x₀ p G.hom m H hU hx`. Establish `hWq : W ≤ q.opensRange` using `hr ▸ hWU`. Establish `: IsIso (q.app W)` using `q.isIso_app W hWq`. Set `e : Γ(X, W) ≃+* Γ(X', q ⁻¹ᵁ W)` to `(asIso (q.app W)).commRingCatIsoToRingEquiv`.

Establish `he : ∀ f, e f = (q.app W).hom f` using `fun _ => rfl`. Establish `key : ∀ f, ((m' ≫ q).app W).hom f = (m'.app (q ⁻¹ᵁ W)).hom (e f)` using `fun _ => rfl`. Take `⟨c, hc, hu⟩` from `GlobalTheory.InvFieldBasis.existsUnique_coeff_alg hv hd x₀' p' m' H' y (hW.preimage_of_isOpenImmersion q hWq) h (fun f' => δ (e.symm f')) (fun f f' => by rw [map_add, hadd]) (fun f f' => by`. Take `⟨f, rfl⟩` from `e.surjective f`. Take `⟨f', rfl⟩` from `e.surjective f'`.

Rewrite using `[← map_mul, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply, hmul, key, key]`. Use the proof step `rfl)`. Use the proof step `(fun r => by rw [← hb W hWU r, ← he, e.symm_apply_apply, hbase])`. Use `⟨c, fun f => ?_, fun c' hc' => hu c' fun f' => ?_⟩` and prove the remaining obligations. Use `hc (e f)` as an intermediate fact.

Rewrite `this` using `[e.symm_apply_apply]`. Rewrite using `[this]`. Both sides reduce to the same expression. Take `⟨f, rfl⟩` from `e.surjective f'`. Rewrite using `[e.symm_apply_apply, hc' f]`.

Both sides reduce to the same expression. Establish `: Subsingleton C`. Assume the negation of the conclusion as `hC`. Rewrite `hC` using `[not_subsingleton_iff_nontrivial]`. Take `⟨P⟩ : Nonempty (PrimeSpectrum C)` from `inferInstance`.

Conclude with `false_of_pullback_point_mem_preimage_of_not_univ_le x₀ p G.hom m H hx y.left hWU P (@h P trivial)`. Conclude with `⟨0, fun _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩`.
-/
theorem existsUnique_coeff_alg [Smooth G.hom] {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    {dd : Fin n → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : ∀ i, IsInvDer (v i) (dd i))
    {S : Scheme.{0}} (x₀ : Sp K ⟶ S) {X : Scheme.{0}} (p : X ⟶ S) (m : G.left ⟶ X)
    (H : IsPullback m G.hom p x₀) {U : S.Opens} (hU : IsAffineOpen U) (y : sp (R₀ := K) C ⟶ G) {W : X.Opens} (hW : IsAffineOpen W) (hWU : W ≤ p ⁻¹ᵁ U)
    (h : ⊤ ≤ y.left ⁻¹ᵁ (m ⁻¹ᵁ W)) (δ : Γ(X, W) → C) (hadd : ∀ f f', δ (f + f') = δ f + δ f')
    (hmul : ∀ f f', δ (f * f') = evalPt y.left _ h ((m.app W).hom f) * δ f' +
      evalPt y.left _ h ((m.app W).hom f') * δ f)
    (hbase : ∀ r : Γ(S, U), δ (pbT p r W) = 0) :
    ∃! c : Fin n → C, ∀ f, δ f = ∑ a, c a * evalPt y.left _ h (dd a _ ((m.app W).hom f)) := by
  by_cases hx : ⊤ ≤ x₀ ⁻¹ᵁ U
  · obtain ⟨X', p', q, hq, m', x₀', rfl, H', hr, hb⟩ := exists_openImmersion_restrict_pullback_constFn x₀ p G.hom m H hU hx
    have hWq : W ≤ q.opensRange := hr ▸ hWU
    have : IsIso (q.app W) := q.isIso_app W hWq
    let e : Γ(X, W) ≃+* Γ(X', q ⁻¹ᵁ W) := (asIso (q.app W)).commRingCatIsoToRingEquiv
    have he : ∀ f, e f = (q.app W).hom f := fun _ => rfl
    have key : ∀ f, ((m' ≫ q).app W).hom f = (m'.app (q ⁻¹ᵁ W)).hom (e f) := fun _ => rfl
    obtain ⟨c, hc, hu⟩ := GlobalTheory.InvFieldBasis.existsUnique_coeff_alg hv hd x₀' p' m' H' y
      (hW.preimage_of_isOpenImmersion q hWq) h (fun f' => δ (e.symm f'))
      (fun f f' => by rw [map_add, hadd])
      (fun f f' => by
        obtain ⟨f, rfl⟩ := e.surjective f
        obtain ⟨f', rfl⟩ := e.surjective f'
        rw [← map_mul, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply, hmul, key, key]
        rfl)
      (fun r => by rw [← hb W hWU r, ← he, e.symm_apply_apply, hbase])
    refine ⟨c, fun f => ?_, fun c' hc' => hu c' fun f' => ?_⟩
    · have := hc (e f)
      rw [e.symm_apply_apply] at this
      rw [this]
      rfl
    · obtain ⟨f, rfl⟩ := e.surjective f'
      rw [e.symm_apply_apply, hc' f]
      rfl
  · have : Subsingleton C := by
      by_contra hC
      rw [not_subsingleton_iff_nontrivial] at hC
      obtain ⟨P⟩ : Nonempty (PrimeSpectrum C) := inferInstance
      exact false_of_pullback_point_mem_preimage_of_not_univ_le x₀ p G.hom m H hx y.left hWU P (@h P trivial)
    exact ⟨0, fun _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩

/- English proof (translation)
Distinguish the cases in `hx : ⊤ ≤ x₀ ⁻¹ᵁ U`. Take `⟨X', p', q, hq, m', x₀', rfl, H', hr, hb⟩` from `exists_openImmersion_restrict_pullback_constFn x₀ p G.hom m H hU hx`. Establish `hWq : W ≤ q.opensRange` using `hr ▸ hWU`. Establish `: IsIso (q.app W)` using `q.isIso_app W hWq`. Set `e : Γ(X, W) ≃+* Γ(X', q ⁻¹ᵁ W)` to `(asIso (q.app W)).commRingCatIsoToRingEquiv`.

Establish `he : ∀ f, e f = (q.app W).hom f` using `fun _ => rfl`. Establish `key : ∀ f, ((m' ≫ q).app W).hom f = (m'.app (q ⁻¹ᵁ W)).hom (e f)` using `fun _ => rfl`. Take `⟨c, hc, hu⟩` from `GlobalTheory.InvFieldBasis.existsUnique_coeff_affine hv hd x₀' p' m' H' y (hW.preimage_of_isOpenImmersion q hWq) hV h (fun f' => δ (e.symm f')) (fun f f' => by rw [map_add, hadd]) (fun f f' => by`. Take `⟨f, rfl⟩` from `e.surjective f`. Take `⟨f', rfl⟩` from `e.surjective f'`.

Rewrite using `[← map_mul, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply, hmul, key, key]`. Use the proof step `rfl)`. Use the proof step `(fun r => by rw [← hb W hWU r, ← he, e.symm_apply_apply, hbase])`. Use `⟨c, fun f => ?_, fun c' hc' => hu c' fun f' => ?_⟩` and prove the remaining obligations. Use `hc (e f)` as an intermediate fact.

Rewrite `this` using `[e.symm_apply_apply]`. Rewrite using `[this]`. Both sides reduce to the same expression. Take `⟨f, rfl⟩` from `e.surjective f'`. Rewrite using `[e.symm_apply_apply, hc' f]`.

Both sides reduce to the same expression. Establish `hV0 : V = ⊥` using `eq_bot_iff.2 fun t ht => (false_of_pullback_point_mem_preimage_of_not_univ_le x₀ p G.hom m H hx y hWU t (@h t ht)).elim`. Establish `: Subsingleton Γ(T, V)` using `CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty hV0)`. Conclude with `⟨0, fun _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩`.
-/
theorem existsUnique_coeff_affine [Smooth G.hom] {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    {dd : Fin n → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : ∀ i, IsInvDer (v i) (dd i))
    {S : Scheme.{0}} (x₀ : Sp K ⟶ S) {X : Scheme.{0}} (p : X ⟶ S) (m : G.left ⟶ X)
    (H : IsPullback m G.hom p x₀) {U : S.Opens} (hU : IsAffineOpen U) {T : Scheme.{0}} (y : T ⟶ G.left) {W : X.Opens} (hW : IsAffineOpen W) (hWU : W ≤ p ⁻¹ᵁ U)
    {V : T.Opens} (hV : IsAffineOpen V) (h : V ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W)) (δ : Γ(X, W) → Γ(T, V))
    (hadd : ∀ f f', δ (f + f') = δ f + δ f')
    (hmul : ∀ f f', δ (f * f') = pbT y ((m.app W).hom f) V * δ f' + pbT y ((m.app W).hom f') V * δ f)
    (hbase : ∀ r : Γ(S, U), δ (pbT p r W) = 0) :
    ∃! c : Fin n → Γ(T, V), ∀ f, δ f = ∑ a, c a * pbT y (dd a _ ((m.app W).hom f)) V := by
  by_cases hx : ⊤ ≤ x₀ ⁻¹ᵁ U
  · obtain ⟨X', p', q, hq, m', x₀', rfl, H', hr, hb⟩ := exists_openImmersion_restrict_pullback_constFn x₀ p G.hom m H hU hx
    have hWq : W ≤ q.opensRange := hr ▸ hWU
    have : IsIso (q.app W) := q.isIso_app W hWq
    let e : Γ(X, W) ≃+* Γ(X', q ⁻¹ᵁ W) := (asIso (q.app W)).commRingCatIsoToRingEquiv
    have he : ∀ f, e f = (q.app W).hom f := fun _ => rfl
    have key : ∀ f, ((m' ≫ q).app W).hom f = (m'.app (q ⁻¹ᵁ W)).hom (e f) := fun _ => rfl
    obtain ⟨c, hc, hu⟩ := GlobalTheory.InvFieldBasis.existsUnique_coeff_affine hv hd x₀' p' m' H' y
      (hW.preimage_of_isOpenImmersion q hWq) hV h (fun f' => δ (e.symm f'))
      (fun f f' => by rw [map_add, hadd])
      (fun f f' => by
        obtain ⟨f, rfl⟩ := e.surjective f
        obtain ⟨f', rfl⟩ := e.surjective f'
        rw [← map_mul, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply, hmul, key, key]
        rfl)
      (fun r => by rw [← hb W hWU r, ← he, e.symm_apply_apply, hbase])
    refine ⟨c, fun f => ?_, fun c' hc' => hu c' fun f' => ?_⟩
    · have := hc (e f)
      rw [e.symm_apply_apply] at this
      rw [this]
      rfl
    · obtain ⟨f, rfl⟩ := e.surjective f'
      rw [e.symm_apply_apply, hc' f]
      rfl
  · have hV0 : V = ⊥ := eq_bot_iff.2 fun t ht => (false_of_pullback_point_mem_preimage_of_not_univ_le x₀ p G.hom m H hx y hWU t (@h t ht)).elim
    have : Subsingleton Γ(T, V) :=
      CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty hV0)
    exact ⟨0, fun _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩

/- English proof (translation)
Rewrite using `[resG, resG, resG, ← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
private theorem resG_resG_divisor {Y : Scheme.{0}} {O O₁ O₂ : Y.Opens} (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O₁)
    (s : Γ(Y, O)) : resG Y h₂ (resG Y h₁ s) = resG Y (h₂.trans h₁) s := by
  rw [resG, resG, resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Rewrite using `[rsT, dif_pos h]`.
-/
private theorem rsT_eq_resG_of_le {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) {O : Y.Opens} (h : O ≤ O₀) :
    rsT s O = resG Y h s := by
  rw [rsT, dif_pos h]

/- English proof (translation)
Simplify using `[resG]`.
-/
private theorem resG_self_eq {Y : Scheme.{0}} {O : Y.Opens} (h : O ≤ O) (s : Γ(Y, O)) :
    resG Y h s = s := by
  simp [resG]

/- English proof (translation)
Rewrite using `[pbT, pbT, dif_pos hO, dif_pos (h.trans hO), ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]`.
-/
private theorem resG_pbT_eq_pbT_of_le {Z Y : Scheme.{0}} (y : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀))
    {O O' : Z.Opens} (h : O' ≤ O) (hO : O ≤ y ⁻¹ᵁ O₀) : resG Z h (pbT y s O) = pbT y s O' := by
  rw [pbT, pbT, dif_pos hO, dif_pos (h.trans hO), ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/- English proof (translation)
Substitute `h` using the available equality. Simplify using the standard rewrite rules.
-/
private theorem pbT_app_presheaf_map_eqToHom_eq {Z Y T' : Scheme.{0}} (F : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (m' : Z ⟶ Y)
    (y : T' ⟶ Z) {O O' : Y.Opens} (h : O' = O) (f : Γ(Y, O)) (V : T'.Opens) :
    pbT y (F (m' ⁻¹ᵁ O') ((m'.app O').hom ((Y.presheaf.map (eqToHom h).op).hom f))) V =
      pbT y (F (m' ⁻¹ᵁ O) ((m'.app O).hom f)) V := by
  subst h
  simp

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[resG_self_eq]`. Simplify using the standard rewrite rules.
-/
private theorem resG_app_presheaf_map_eqToHom_eq_app {Z Y : Scheme.{0}} (F : Z ⟶ Y) {O O' : Y.Opens} (h : O' = O)
    (hh : F ⁻¹ᵁ O ≤ F ⁻¹ᵁ O') (f : Γ(Y, O)) :
    resG Z hh ((F.app O').hom ((Y.presheaf.map (eqToHom h).op).hom f)) = (F.app O).hom f := by
  subst h
  rw [resG_self_eq]
  simp

/- English proof (translation)
Use `(asIso (q.app (q ''ᵁ (q ⁻¹ᵁ W)))).commRingCatIsoToRingEquiv.injective ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(q.app _).hom ((q.appIso (q ⁻¹ᵁ W)).inv.hom ((q.app W).hom f)) = (q.app _).hom ((Y.presheaf.map (homOfLE h).op).hom f)`. Establish `h1` using `congrArg (fun φ => φ.hom ((q.app W).hom f)) (Scheme.Hom.appIso_inv_app q (q ⁻¹ᵁ W))`. Establish `h2` using `congrArg (fun φ => φ.hom f) (q.naturality (homOfLE h).op)`. Simplify using `only [CommRingCat.comp_apply] at h1 h2`.

Rewrite using `[h1]`. Use `erw [h2]`. Conclude with `congrArg (fun i => (Z.presheaf.map i).hom ((q.app W).hom f)) (Subsingleton.elim _ _)`.
-/
private theorem appIso_inv_app_eq_resG_of_isOpenImmersion {Y Z : Scheme.{0}} (q : Z ⟶ Y) [IsOpenImmersion q] (W : Y.Opens)
    (h : q ''ᵁ (q ⁻¹ᵁ W) ≤ W) (f : Γ(Y, W)) :
    (q.appIso (q ⁻¹ᵁ W)).inv.hom ((q.app W).hom f) = resG Y h f := by
  refine (asIso (q.app (q ''ᵁ (q ⁻¹ᵁ W)))).commRingCatIsoToRingEquiv.injective ?_
  change (q.app _).hom ((q.appIso (q ⁻¹ᵁ W)).inv.hom ((q.app W).hom f)) =
    (q.app _).hom ((Y.presheaf.map (homOfLE h).op).hom f)
  have h1 := congrArg (fun φ => φ.hom ((q.app W).hom f)) (Scheme.Hom.appIso_inv_app q (q ⁻¹ᵁ W))
  have h2 := congrArg (fun φ => φ.hom f) (q.naturality (homOfLE h).op)
  simp only [CommRingCat.comp_apply] at h1 h2
  rw [h1]
  erw [h2]
  exact congrArg (fun i => (Z.presheaf.map i).hom ((q.app W).hom f)) (Subsingleton.elim _ _)

/- English proof (translation)
Distinguish the cases in `hx : ⊤ ≤ x₀ ⁻¹ᵁ U`. Take `⟨X', p', q, hq, m', x₀', rfl, H', hr, hb⟩` from `exists_openImmersion_restrict_pullback_constFn x₀ p A₀.hom m H hU hx`. Establish `hle : ∀ W' : X'.Opens, W' ≤ q ⁻¹ᵁ W₀ → q ''ᵁ W' ≤ W₀` using `fun W' h => ((Scheme.Hom.image_le_image_iff q W' _).2 h).trans (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_le_right)`. Establish `hO : ∀ W' : X'.Opens, (y ≫ m') ⁻¹ᵁ W' ≤ (y ≫ m' ≫ q) ⁻¹ᵁ (q ''ᵁ W')` using `fun W' t ht => by show q (m' (y t)) ∈ q ''ᵁ W'`. Conclude with `(Scheme.Hom.apply_mem_image_iff q).2 ht`.

Establish `K1 : ∀ (W' : X'.Opens) (f : Γ(X', W')), resG T (hO W') (((y ≫ m' ≫ q).app (q ''ᵁ W')).hom ((q.appIso W').inv.hom f)) = ((y ≫ m').app W').hom f`. Introduce `W' f`. Establish `h1` using `congrArg (fun φ => φ.hom f) (Scheme.Hom.appIso_inv_app q W')`. Simplify using `only [CommRingCat.comp_apply] at h1`. Establish `h2 : ((y ≫ m' ≫ q).app (q ''ᵁ W')).hom ((q.appIso W').inv.hom f) = ((y ≫ m').app (q ⁻¹ᵁ (q ''ᵁ W'))).hom ((q.app (q ''ᵁ W')).hom ((q.appIso W').inv.hom f))`.

Both sides reduce to the same expression. Rewrite using `[h2, h1]`. Conclude with `resG_app_presheaf_map_eqToHom_eq_app (y ≫ m') (q.preimage_image_eq W') _ f`. Establish `K2 : ∀ (W' : X'.Opens) (r : Γ(S, U)), q ''ᵁ W' ≤ p ⁻¹ᵁ U → (q.appIso W').inv.hom (constFn p' W' r) = pbT p r (q ''ᵁ W')`. Introduce `W' r hW'`.

Establish `h1 : (q.appIso W').hom.hom (pbT p r (q ''ᵁ W')) = constFn p' W' r`. Rewrite using `[Scheme.Hom.appIso_hom, CommRingCat.comp_apply, hb _ hW']`. Simplify using `only [constFn]`. Rewrite using `[← CommRingCat.comp_apply]`. Use `erw [Scheme.Hom.appLE_map]`.

Rewrite using `[← h1, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]`. Set `d' : ∀ W' : X'.Opens, Γ(X', W') → Γ(T, (y ≫ m') ⁻¹ᵁ W')` to `fun W' f => resG T (hO W') (d (q ''ᵁ W') ((q.appIso W').inv.hom f))`. Establish `hL : LocDerK (y ≫ A₀.hom) p' (y ≫ m') (fun _ => 0) (q ⁻¹ᵁ W₀) d'`. Use `⟨fun W' hW' f f' => ?_, fun W' hW' f f' => ?_, fun W₁ W₂ h₂ hW₁ f => ?_, fun W' hW' r => ?_⟩` and prove the remaining obligations. Simplify using `only [d', map_add, hadd _ (hle W' hW')]`.

Simplify using `only [d', map_mul, hmul _ (hle W' hW'), map_add, K1]`. Simplify using `only [d']`. Establish `hh : q ''ᵁ W₂ ≤ q ''ᵁ W₁` using `(Scheme.Hom.image_le_image_iff q W₂ W₁).2 h₂`. Establish `hi` using `congrArg (fun φ => φ.hom f) (Scheme.Hom.appIso_inv_naturality q (homOfLE h₂).op)`. Simplify using `only [CommRingCat.comp_apply] at hi`.

Rewrite using `[hi]`. Use `erw [hrs _ _ hh (hle W₁ hW₁)]`. Rewrite using `[rsT_eq_resG_of_le _ ((y ≫ m' ≫ q).preimage_mono hh), rsT_eq_resG_of_le _ ((y ≫ m').preimage_mono h₂), resG_resG_divisor, resG_resG_divisor]`. Simplify using `only [d']`. Rewrite using `[K2 W' r ((hle W' hW').trans hW₀), hbase _ (hle W' hW'), map_zero]`.

Simplify using `only [constFn, map_zero]`. Take `⟨c, hc, hu⟩` from `GlobalTheory.InvFieldBasis.existsUnique_coeff K A₀ g v dd hs hv hd Γ(S, U) x₀' X' p' m' H' T y (q ⁻¹ᵁ W₀) d' hL`. Establish `K3 : ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), d' (q ⁻¹ᵁ W) ((q.app W).hom f) = d W f`. Introduce `W hW f`. Establish `hWr : q ''ᵁ (q ⁻¹ᵁ W) ≤ W`.

Rewrite using `[Scheme.Hom.image_preimage_eq_opensRange_inf]`. Conclude with `inf_le_right`. Establish `h1` using `appIso_inv_app_eq_resG_of_isOpenImmersion q W hWr f`. Simplify using `only [d']`. Rewrite using `[h1, hrs W _ hWr hW, rsT_eq_resG_of_le _ ((y ≫ m' ≫ q).preimage_mono hWr), resG_resG_divisor]`.

Conclude with `resG_self_eq _ _`. Use `⟨c, fun W hW f => ?_, fun c' hc' => hu c' fun W' hW' f' => ?_⟩` and prove the remaining obligations. Rewrite using `[← K3 W hW f, hc _ (q.preimage_mono hW)]`. Both sides reduce to the same expression. Establish `h1` using `hc' (q ''ᵁ W') (hle W' hW') ((q.appIso W').inv.hom f') show resG T (hO W') (d (q ''ᵁ W') ((q.appIso W').inv.hom f')) = _`.

Rewrite using `[h1, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `hA : (y ≫ m' ≫ q) ⁻¹ᵁ (q ''ᵁ W') ≤ (y ≫ m' ≫ q) ⁻¹ᵁ W₀` using `(y ≫ m' ≫ q).preimage_mono (hle W' hW')`. Establish `hφ : ((m' ≫ q).app (q ''ᵁ W')).hom ((q.appIso W').inv.hom f') = (m'.app (q ⁻¹ᵁ (q ''ᵁ W'))).hom ((X'.presheaf.map (eqToHom (q.preimage_image_eq W')).op).hom f')`. Rewrite using `[← Scheme.Hom.appIso_inv_app]`.

Both sides reduce to the same expression. Rewrite using `[map_mul, rsT_eq_resG_of_le (c' a) hA, resG_resG_divisor, resG_pbT_eq_pbT_of_le y (O₀ := (m' ≫ q) ⁻¹ᵁ (q ''ᵁ W')) _ (hO W') le_rfl]`. Use `congr 1`. Conclude with `(rsT_eq_resG_of_le (c' a) _).symm`. Rewrite using `[hφ]`.

Conclude with `pbT_app_presheaf_map_eqToHom_eq (dd a) m' y (q.preimage_image_eq W') f' _`. Establish `h0 : (y ≫ m) ⁻¹ᵁ W₀ = ⊥` using `eq_bot_iff.2 fun t ht => (false_of_pullback_point_mem_preimage_of_not_univ_le x₀ p A₀.hom m H hx y hW₀ t ht).elim`. Establish `: Subsingleton Γ(T, (y ≫ m) ⁻¹ᵁ W₀)` using `CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty h0)`. Use `⟨0, fun W hW f => ?_, fun _ _ => Subsingleton.elim _ _⟩` and prove the remaining obligations. Establish `hW0 : (y ≫ m) ⁻¹ᵁ W = ⊥` using `eq_bot_iff.2 fun t ht => (false_of_pullback_point_mem_preimage_of_not_univ_le x₀ p A₀.hom m H hx y (hW.trans hW₀) t ht).elim`.

Establish `: Subsingleton Γ(T, (y ≫ m) ⁻¹ᵁ W)` using `CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty hW0)`. Conclude with `Subsingleton.elim _ _`.
-/
theorem existsUnique_coeff {A₀ : Over (Sp K)} [GrpObj A₀] {g : ℕ} {v : Fin g → (epsR K ⟶ A₀)}
    {dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)} (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) {S : Scheme.{0}} (x₀ : Sp K ⟶ S) {X : Scheme.{0}} (p : X ⟶ S) (m : A₀.left ⟶ X)
    (H : IsPullback m A₀.hom p x₀) {U : S.Opens} (hU : IsAffineOpen U) {T : Scheme.{0}} (y : T ⟶ A₀.left)
    (W₀ : X.Opens) (hW₀ : W₀ ≤ p ⁻¹ᵁ U) (d : ∀ W : X.Opens, Γ(X, W) → Γ(T, (y ≫ m) ⁻¹ᵁ W))
    (hadd : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f')
    (hmul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = ((y ≫ m).app W).hom f * d W f' + ((y ≫ m).app W).hom f' * d W f)
    (hrs : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) ((y ≫ m) ⁻¹ᵁ W'))
    (hbase : ∀ W, W ≤ W₀ → ∀ r : Γ(S, U), d W (pbT p r W) = 0) :
    ∃! c : Fin g → Γ(T, (y ≫ m) ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
  by_cases hx : ⊤ ≤ x₀ ⁻¹ᵁ U
  · obtain ⟨X', p', q, hq, m', x₀', rfl, H', hr, hb⟩ := exists_openImmersion_restrict_pullback_constFn x₀ p A₀.hom m H hU hx
    have hle : ∀ W' : X'.Opens, W' ≤ q ⁻¹ᵁ W₀ → q ''ᵁ W' ≤ W₀ := fun W' h =>
      ((Scheme.Hom.image_le_image_iff q W' _).2 h).trans
        (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_le_right)
    have hO : ∀ W' : X'.Opens, (y ≫ m') ⁻¹ᵁ W' ≤ (y ≫ m' ≫ q) ⁻¹ᵁ (q ''ᵁ W') := fun W' t ht => by
      show q (m' (y t)) ∈ q ''ᵁ W'
      exact (Scheme.Hom.apply_mem_image_iff q).2 ht
    have K1 : ∀ (W' : X'.Opens) (f : Γ(X', W')), resG T (hO W')
        (((y ≫ m' ≫ q).app (q ''ᵁ W')).hom ((q.appIso W').inv.hom f)) = ((y ≫ m').app W').hom f := by
      intro W' f
      have h1 := congrArg (fun φ => φ.hom f) (Scheme.Hom.appIso_inv_app q W')
      simp only [CommRingCat.comp_apply] at h1
      have h2 : ((y ≫ m' ≫ q).app (q ''ᵁ W')).hom ((q.appIso W').inv.hom f) =
          ((y ≫ m').app (q ⁻¹ᵁ (q ''ᵁ W'))).hom ((q.app (q ''ᵁ W')).hom ((q.appIso W').inv.hom f)) :=
        rfl
      rw [h2, h1]
      exact resG_app_presheaf_map_eqToHom_eq_app (y ≫ m') (q.preimage_image_eq W') _ f
    have K2 : ∀ (W' : X'.Opens) (r : Γ(S, U)), q ''ᵁ W' ≤ p ⁻¹ᵁ U →
        (q.appIso W').inv.hom (constFn p' W' r) = pbT p r (q ''ᵁ W') := by
      intro W' r hW'
      have h1 : (q.appIso W').hom.hom (pbT p r (q ''ᵁ W')) = constFn p' W' r := by
        rw [Scheme.Hom.appIso_hom, CommRingCat.comp_apply, hb _ hW']
        simp only [constFn]
        rw [← CommRingCat.comp_apply]
        erw [Scheme.Hom.appLE_map]
      rw [← h1, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    let d' : ∀ W' : X'.Opens, Γ(X', W') → Γ(T, (y ≫ m') ⁻¹ᵁ W') := fun W' f =>
      resG T (hO W') (d (q ''ᵁ W') ((q.appIso W').inv.hom f))
    have hL : LocDerK (y ≫ A₀.hom) p' (y ≫ m') (fun _ => 0) (q ⁻¹ᵁ W₀) d' := by
      refine ⟨fun W' hW' f f' => ?_, fun W' hW' f f' => ?_, fun W₁ W₂ h₂ hW₁ f => ?_,
        fun W' hW' r => ?_⟩
      · simp only [d', map_add, hadd _ (hle W' hW')]
      · simp only [d', map_mul, hmul _ (hle W' hW'), map_add, K1]
      · simp only [d']
        have hh : q ''ᵁ W₂ ≤ q ''ᵁ W₁ := (Scheme.Hom.image_le_image_iff q W₂ W₁).2 h₂
        have hi := congrArg (fun φ => φ.hom f) (Scheme.Hom.appIso_inv_naturality q (homOfLE h₂).op)
        simp only [CommRingCat.comp_apply] at hi
        rw [hi]
        erw [hrs _ _ hh (hle W₁ hW₁)]
        rw [rsT_eq_resG_of_le _ ((y ≫ m' ≫ q).preimage_mono hh), rsT_eq_resG_of_le _ ((y ≫ m').preimage_mono h₂),
          resG_resG_divisor, resG_resG_divisor]
      · simp only [d']
        rw [K2 W' r ((hle W' hW').trans hW₀), hbase _ (hle W' hW'), map_zero]
        simp only [constFn, map_zero]
    obtain ⟨c, hc, hu⟩ := GlobalTheory.InvFieldBasis.existsUnique_coeff K A₀ g v dd hs hv hd Γ(S, U) x₀' X' p'
      m' H' T y (q ⁻¹ᵁ W₀) d' hL
    have K3 : ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), d' (q ⁻¹ᵁ W) ((q.app W).hom f) = d W f := by
      intro W hW f
      have hWr : q ''ᵁ (q ⁻¹ᵁ W) ≤ W := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_le_right
      have h1 := appIso_inv_app_eq_resG_of_isOpenImmersion q W hWr f
      simp only [d']
      rw [h1, hrs W _ hWr hW, rsT_eq_resG_of_le _ ((y ≫ m' ≫ q).preimage_mono hWr), resG_resG_divisor]
      exact resG_self_eq _ _
    refine ⟨c, fun W hW f => ?_, fun c' hc' => hu c' fun W' hW' f' => ?_⟩
    · rw [← K3 W hW f, hc _ (q.preimage_mono hW)]
      rfl
    · have h1 := hc' (q ''ᵁ W') (hle W' hW') ((q.appIso W').inv.hom f')
      show resG T (hO W') (d (q ''ᵁ W') ((q.appIso W').inv.hom f')) = _
      rw [h1, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hA : (y ≫ m' ≫ q) ⁻¹ᵁ (q ''ᵁ W') ≤ (y ≫ m' ≫ q) ⁻¹ᵁ W₀ :=
        (y ≫ m' ≫ q).preimage_mono (hle W' hW')
      have hφ : ((m' ≫ q).app (q ''ᵁ W')).hom ((q.appIso W').inv.hom f') =
          (m'.app (q ⁻¹ᵁ (q ''ᵁ W'))).hom
            ((X'.presheaf.map (eqToHom (q.preimage_image_eq W')).op).hom f') := by
        rw [← Scheme.Hom.appIso_inv_app]
        rfl
      rw [map_mul, rsT_eq_resG_of_le (c' a) hA, resG_resG_divisor, resG_pbT_eq_pbT_of_le y (O₀ := (m' ≫ q) ⁻¹ᵁ (q ''ᵁ W')) _
        (hO W') le_rfl]
      congr 1
      · exact (rsT_eq_resG_of_le (c' a) _).symm
      · rw [hφ]
        exact pbT_app_presheaf_map_eqToHom_eq (dd a) m' y (q.preimage_image_eq W') f' _
  · have h0 : (y ≫ m) ⁻¹ᵁ W₀ = ⊥ :=
      eq_bot_iff.2 fun t ht => (false_of_pullback_point_mem_preimage_of_not_univ_le x₀ p A₀.hom m H hx y hW₀ t ht).elim
    have : Subsingleton Γ(T, (y ≫ m) ⁻¹ᵁ W₀) :=
      CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty h0)
    refine ⟨0, fun W hW f => ?_, fun _ _ => Subsingleton.elim _ _⟩
    have hW0 : (y ≫ m) ⁻¹ᵁ W = ⊥ := eq_bot_iff.2 fun t ht =>
      (false_of_pullback_point_mem_preimage_of_not_univ_le x₀ p A₀.hom m H hx y (hW.trans hW₀) t ht).elim
    have : Subsingleton Γ(T, (y ≫ m) ⁻¹ᵁ W) :=
      CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty hW0)
    exact Subsingleton.elim _ _

end GlobalTheory.KSUniq
